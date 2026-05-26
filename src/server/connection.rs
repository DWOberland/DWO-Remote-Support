#[cfg(target_os = "windows")]
use super::login_failure_check::try_acquire_os_credential_login_gate;
use super::login_failure_check::{
    evaluate_os_credential_policy, record_os_credential_failure, FailureScope,
};
use super::{input_service::*, *};
#[cfg(feature = "unix-file-copy-paste")]
use crate::clipboard::try_empty_clipboard_files;
#[cfg(not(any(target_os = "android", target_os = "ios")))]
use crate::clipboard::{update_clipboard, ClipboardSide};
#[cfg(any(target_os = "windows", target_os = "linux", target_os = "macos"))]
use crate::clipboard_file::*;
#[cfg(target_os = "android")]
use crate::keyboard::client::map_key_to_control_key;
#[cfg(target_os = "linux")]
use crate::platform::linux_desktop_manager;
#[cfg(any(target_os = "windows", target_os = "linux"))]
use crate::platform::WallPaperRemover;
#[cfg(windows)]
use crate::portable_service::client as portable_client;
use crate::{
    client::{
        new_voice_call_request, new_voice_call_response, start_audio_thread, MediaData, MediaSender,
    },
    display_service, ipc, privacy_mode, video_service, VERSION,
};
#[cfg(any(target_os = "android", target_os = "ios"))]
use crate::{common::DEVICE_NAME, flutter::connection_manager::start_channel};
use cidr_utils::cidr::IpCidr;
#[cfg(target_os = "android")]
use hbb_common::protobuf::EnumOrUnknown;
use hbb_common::{
    config::{
        self, decode_permanent_password_h1_from_storage, decode_preset_password_h1_from_storage,
        keys, local_permanent_password_storage_is_usable_for_auth,
        preset_permanent_password_storage_is_usable_for_auth, Config, TrustedDevice,
    },
    fs::{self, can_enable_overwrite_detection, JobType},
    futures::{SinkExt, StreamExt},
    get_time, get_version_number,
    message_proto::{option_message::BoolOption, permission_info::Permission},
    password_security::{self as password, ApproveMode},
    sha2::{Digest, Sha256},
    sleep, timeout,
    tokio::{
        net::TcpStream,
        sync::mpsc,
        time::{self, Duration, Instant},
    },
    tokio_util::codec::{BytesCodec, Framed},
};
#[cfg(any(target_os = "android", target_os = "ios"))]
use scrap::android::{call_main_service_key_event, call_main_service_pointer_input};
use scrap::camera;
use serde_derive::Serialize;
use serde_json::{json, value::Value};
#[cfg(not(any(target_os = "android", target_os = "ios")))]
use std::sync::atomic::Ordering;
use std::{
    collections::HashSet,
    net::Ipv6Addr,
    num::NonZeroI64,
    path::PathBuf,
    str::FromStr,
    sync::{atomic::AtomicI64, mpsc as std_mpsc},
};
#[cfg(not(any(target_os = "android", target_os = "ios")))]
use system_shutdown;
#[cfg(target_os = "windows")]
use windows::Win32::Foundation::{CloseHandle, HANDLE};

#[cfg(windows)]
use crate::virtual_display_manager;
pub type Sender = mpsc::UnboundedSender<(Instant, Arc<Message>)>;

lazy_static::lazy_static! {
    static ref LOGIN_FAILURES: [Arc::<Mutex<HashMap<String, (i32, i32, i32)>>>; 2] = Default::default();
    static ref SESSIONS: Arc::<Mutex<HashMap<SessionKey, Session>>> = Default::default();
    static ref ALIVE_CONNS: Arc::<Mutex<Vec<i32>>> = Default::default();
    pub static ref AUTHED_CONNS: Arc::<Mutex<Vec<AuthedConn>>> = Default::default();
    pub static ref CONTROL_PERMISSIONS_ARRAY: Arc::<Mutex<Vec<(i32, ControlPermissions)>>> = Default::default();
    static ref WAKELOCK_SENDER: Arc::<Mutex<std::sync::mpsc::Sender<(usize, usize)>>> = Arc::new(Mutex::new(start_wakelock_thread()));
    static ref WAKELOCK_KEEP_AWAKE_OPTION: Arc::<Mutex<Option<bool>>> = Default::default();
}

#[cfg(feature = "flutter")]
#[cfg(not(any(target_os = "android", target_os = "ios")))]
lazy_static::lazy_static! {
    static ref SWITCH_SIDES_UUID: Arc::<Mutex<HashMap<String, (Instant, uuid::Uuid)>>> = Default::default();
    static ref PENDING_SWITCH_SIDES_UUID: Arc::<Mutex<HashMap<String, (Instant, uuid::Uuid)>>> = Default::default();
}

#[cfg(target_os = "windows")]
const TERMINAL_OS_LOGIN_FAILED_MSG: &str = "Incorrect username or password.";

fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    // Avoid data-dependent early exits.
    let mut x: u8 = 0;
    for i in 0..a.len() {
        x |= a[i] ^ b[i];
    }
    x == 0
}

#[cfg(target_os = "linux")]
fn should_check_linux_headless_os_auth_before_desktop_start(
    is_headless_allowed: bool,
    username: &str,
) -> bool {
    is_headless_allowed
        && !username.trim().is_empty()
        && linux_desktop_manager::get_username().is_empty()
}

#[cfg(target_os = "linux")]
fn should_record_linux_headless_os_auth_failure(
    is_headless_allowed: bool,
    username: &str,
    err_msg: &str,
) -> bool {
    is_headless_allowed
        && !username.trim().is_empty()
        && err_msg == crate::client::LOGIN_MSG_PASSWORD_WRONG
}

#[cfg(not(any(target_os = "android", target_os = "ios")))]
fn should_use_terminal_os_login_scope(is_terminal: bool, os_login_username: &str) -> bool {
    cfg!(target_os = "windows") && is_terminal && !os_login_username.trim().is_empty()
}

#[cfg(any(target_os = "windows", target_os = "linux"))]
lazy_static::lazy_static! {
    static ref WALLPAPER_REMOVER: Arc<Mutex<Option<WallPaperRemover>>> = Default::default();
}
pub static CLICK_TIME: AtomicI64 = AtomicI64::new(0);
#[cfg(not(any(target_os = "android", target_os = "ios")))]
pub static MOUSE_MOVE_TIME: AtomicI64 = AtomicI64::new(0);

#[cfg(all(feature = "flutter", feature = "plugin_framework"))]
#[cfg(not(any(target_os = "android", target_os = "ios")))]
lazy_static::lazy_static! {
    static ref PLUGIN_BLOCK_INPUT_TXS: Arc<Mutex<HashMap<String, std_mpsc::Sender<MessageInput>>>> = Default::default();
    static ref PLUGIN_BLOCK_INPUT_TX_RX: (Arc<Mutex<std_mpsc::Sender<bool>>>, Arc<Mutex<std_mpsc::Receiver<bool>>>) = {
        let (tx, rx) = std_mpsc::channel();
        (Arc::new(Mutex::new(tx)), Arc::new(Mutex::new(rx)))
    };
}

// Block input is required for some special cases, such as privacy mode.
#[cfg(all(feature = "flutter", feature = "plugin_framework"))]
#[cfg(not(any(target_os = "android", target_os = "ios")))]
pub fn plugin_block_input(peer: &str, block: bool) -> bool {
    if let Some(tx) = PLUGIN_BLOCK_INPUT_TXS.lock().unwrap().get(peer) {
        let _ = tx.send(if block {
            MessageInput::BlockOnPlugin(peer.to_string())
        } else {
            MessageInput::BlockOffPlugin(peer.to_string())
        });
        match PLUGIN_BLOCK_INPUT_TX_RX
            .1
            .lock()
            .unwrap()
            .recv_timeout(std::time::Duration::from_millis(3_000))
        {
            Ok(b) => b == block,
            Err(..) => {
                log::error!("plugin_block_input timeout");
                false
            }
        }
    } else {
        false
    }
}

#[derive(Clone, Default)]
pub struct ConnInner {
    id: i32,
    tx: Option<Sender>,
    tx_video: Option<Sender>,
}

struct InputMouse {
    msg: MouseEvent,
    conn_id: i32,
    username: String,
    argb: u32,
    simulate: bool,
    show_cursor: bool,
}

enum MessageInput {
    #[cfg(not(any(target_os = "android", target_os = "ios")))]
    Mouse(InputMouse),
    #[cfg(not(any(target_os = "android", target_os = "ios")))]
    Key((KeyEvent, bool)),
    #[cfg(not(any(target_os = "android", target_os = "ios")))]
    Pointer((PointerDeviceEvent, i32)),
    BlockOn,
    BlockOff,
    #[cfg(all(feature = "flutter", feature = "plugin_framework"))]
    #[cfg(not(any(target_os = "android", target_os = "ios")))]
    BlockOnPlugin(String),
    #[cfg(all(feature = "flutter", feature = "plugin_framework"))]
    #[cfg(not(any(target_os = "android", target_os = "ios")))]
    BlockOffPlugin(String),
}

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub struct SessionKey {
    peer_id: String,
    name: String,
    session_id: u64,
}

#[derive(Clone, Debug)]
struct Session {
    last_recv_time: Arc<Mutex<Instant>>,
    random_password: String,
    tfa: bool,
}

#[cfg(not(any(target_os = "android", target_os = "ios")))]
struct StartCmIpcPara {
    rx_to_cm: mpsc::UnboundedReceiver<ipc::Data>,
    tx_from_cm: mpsc::UnboundedSender<ipc::Data>,
    rx_desktop_ready: mpsc::Receiver<()>,
    tx_cm_stream_ready: mpsc::Sender<()>,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum AuthConnType {
    Remote,
    FileTransfer,
    PortForward,
    ViewCamera,
    Terminal,
}

#[cfg(not(any(target_os = "android", target_os = "ios")))]
#[derive(Clone, Debug)]
enum TerminalUserToken {
    SelfUser,
    #[cfg(target_os = "windows")]
    CurrentLogonUser(crate::terminal_service::UserToken),
}

#[cfg(not(any(target_os = "android", target_os = "ios")))]
impl TerminalUserToken {
    fn to_terminal_service_token(&self) -> Option<crate::terminal_service::UserToken> {
        match self {
            TerminalUserToken::SelfUser => None,
            #[cfg(target_os = "windows")]
            TerminalUserToken::CurrentLogonUser(token) => Some(*token),
        }
    }
}
pub struct Connection {
    inner: ConnInner,
    display_idx: usize,
    stream: super::Stream,
    server: super::ServerPtrWeak,
    hash: Hash,
    read_jobs: Vec<fs::TransferJob>,
    timer: crate::RustDeskInterval,
    file_timer: crate::RustDeskInterval,
    file_transfer: Option<(String, bool)>,
    view_camera: bool,
    terminal: bool,
    port_forward_socket: Option<Framed<TcpStream, BytesCodec>>,
    port_forward_address: String,
    tx_to_cm: mpsc::UnboundedSender<ipc::Data>,
    authorized: bool,
    require_2fa: Option<totp_rs::TOTP>,
    keyboard: bool,
    clipboard: bool,
    audio: bool,
    file: bool,
    restart: bool,
    recording: bool,
    block_input: bool,
    privacy_mode: bool,
    control_permissions: Option<ControlPermissions>,
    last_test_delay: Option<Instant>,
    network_delay: u32,
    lock_after_session_end: bool,
    show_remote_cursor: bool,
    // by peer
    ip: String,
    // by peer
    disable_keyboard: bool,
    // by peer
    #[cfg(not(any(target_os = "android", target_os = "ios")))]
    show_my_cursor: bool,
    // by peer
    disable_clipboard: bool,
    // by peer
    disable_audio: bool,
    // by peer
    #[cfg(any(target_os = "windows", target_os = "linux", target_os = "macos"))]
    enable_file_transfer: bool,
    // by peer
    audio_sender: Option<MediaSender>,
    // audio by the remote peer/client
    tx_input: std_mpsc::Sender<MessageInput>,
    // handle input messages
    video_ack_required: bool,
    server_audit_conn: String,
    server_audit_file: String,
    lr: LoginRequest,
    peer_argb: u32,
    session_last_recv_time: Option<Arc<Mutex<Instant>>>,
    chat_unanswered: bool,
    file_transferred: bool,
    #[cfg(windows)]
    portable: PortableState,
    from_switch: bool,
    voice_call_request_timestamp: Option<NonZeroI64>,
    voice_calling: bool,
    options_in_login: Option<OptionMessage>,
    #[cfg(not(any(target_os = "ios")))]
    pressed_modifiers: HashSet<rdev::Key>,
    #[cfg(target_os = "linux")]
    linux_headless_handle: LinuxHeadlessHandle,
    closed: bool,
    #[cfg(not(any(target_os = "android", target_os = "ios")))]
    start_cm_ipc_para: Option<StartCmIpcPara>,
    auto_disconnect_timer: Option<(Instant, u64)>,
    authed_conn_id: Option<self::raii::AuthedConnID>,
    file_remove_log_control: FileRemoveLogControl,
    last_supported_encoding: Option<SupportedEncoding>,
    services_subed: bool,
    delayed_read_dir: Option<(String, bool)>,
    #[cfg(target_os = "macos")]
    retina: Retina,
    follow_remote_cursor: bool,
    follow_remote_window: bool,
    multi_ui_session: bool,
    tx_from_authed: mpsc::UnboundedSender<ipc::Data>,
    printer_data: Vec<(Instant, String, Vec<u8>)>,
    // For post requests that need to be sent sequentially.
    // eg. post_conn_audit
    tx_post_seq: mpsc::UnboundedSender<(String, Value)>,
    // Tracks read job IDs delegated to CM process.
    // When a read job is delegated to CM (via FS::ReadFile), the job id is added here.
    // Used to filter stale responses (FileBlockFromCM, FileReadDone, etc.) for
    // cancelled or unknown jobs.
    cm_read_job_ids: HashSet<i32>,
    terminal_service_id: String,
    terminal_persistent: bool,
    // The user token must be set when terminal is enabled.
    // 0 indicates SYSTEM user
    // other values indicate current user
    #[cfg(not(any(target_os = "android", target_os = "ios")))]
    terminal_user_token: Option<TerminalUserToken>,
    terminal_generic_service: Option<Box<GenericService>>,
}

impl ConnInner {
    pub fn new(id: i32, tx: Option<Sender>, tx_video: Option<Sender>) -> Self {
        Self { id, tx, tx_video }
    }
}

impl Subscriber for ConnInner {
    #[inline]
    fn id(&self) -> i32 {
        self.id
    }

    #[inline]
    fn send(&mut self, msg: Arc<Message>) {
        // Send SwitchDisplay on the same channel as VideoFrame to avoid send order problems.
        let tx_by_video = match &msg.union {
            Some(message::Union::VideoFrame(_)) => true,
            Some(message::Union::Misc(misc)) => match &misc.union {
                Some(misc::Union::SwitchDisplay(_)) => true,
                _ => false,
            },
            _ => false,
        };
        let tx = if tx_by_video {
            self.tx_video.as_mut()
        } else {
            self.tx.as_mut()
        };
        tx.map(|tx| {
            allow_err!(tx.send((Instant::now(), msg)));
        });
    }
}

const TEST_DELAY_TIMEOUT: Duration = Duration::from_secs(1);
const SEC30: Duration = Duration::from_secs(30);
const H1: Duration = Duration::from_secs(3600);
const MILLI1: Duration = Duration::from_millis(1);
const SEND_TIMEOUT_VIDEO: u64 = 12_000;
const SEND_TIMEOUT_OTHER: u64 = SEND_TIMEOUT_VIDEO * 10;
const SESSION_TIMEOUT: Duration = Duration::from_secs(30);

impl Connection {
    pub async fn start(
        addr: SocketAddr,
        stream: super::Stream,
        id: i32,
        server: super::ServerPtrWeak,
        control_permissions: Option<ControlPermissions>,
    ) {
        // Android is not supported yet, so we always set control_permissions to None.
        #[cfg(target_os = "android")]
        let control_permissions = None;
        let _raii_id = raii::ConnectionID::new(id);
        let _raii_control_permissions_id =
            raii::ControlPermissionsID::new(id, &control_permissions);
        let salt = Config::get_effective_permanent_password_salt();
        let hash = Hash {
            salt,
            challenge: Config::get_auto_password(6),
            ..Default::default()
        };
        let (tx_from_cm_holder, mut rx_from_cm) = mpsc::unbounded_channel::<ipc::Data>();
        // holding tx_from_cm_holder to avoid cpu burning of rx_from_cm.recv when all sender closed
        let tx_from_cm = tx_from_cm_holder.clone();
        let (tx_to_cm, rx_to_cm) = mpsc::unbounded_channel::<ipc::Data>();
        let (tx, mut rx) = mpsc::unbounded_channel::<(Instant, Arc<Message>)>();
        let (tx_video, mut rx_video) = mpsc::unbounded_channel::<(Instant, Arc<Message>)>();
        let (tx_input, _rx_input) = std_mpsc::channel();
        let (tx_from_authed, mut rx_from_authed) = mpsc::unbounded_channel::<ipc::Data>();
        let mut hbbs_rx = crate::hbbs_http::sync::signal_receiver();
        #[cfg(not(any(target_os = "android", target_os = "ios")))]
        let (tx_cm_stream_ready, _rx_cm_stream_ready) = mpsc::channel(1);
        #[cfg(not(any(target_os = "android", target_os = "ios")))]
        let (_tx_desktop_ready, rx_desktop_ready) = mpsc::channel(1);
        #[cfg(target_os = "linux")]
        let linux_headless_handle =
            LinuxHeadlessHandle::new(_rx_cm_stream_ready, _tx_desktop_ready);

        let (tx_post_seq, rx_post_seq) = mpsc::unbounded_channel();
        tokio::spawn(async move {
            Self::post_seq_loop(rx_post_seq).await;
        });

        #[cfg(not(any(target_os = "android", target_os = "ios")))]
        let tx_cloned = tx.clone();
        let mut conn = Self {
            inner: ConnInner {
                id,
                tx: Some(tx),
                tx_video: Some(tx_video),
            },
            require_2fa: crate::auth_2fa::get_2fa(None),
            display_idx: *display_service::PRIMARY_DISPLAY_IDX,
            stream,
            server,
            hash,
            read_jobs: Vec::new(),
            timer: crate::rustdesk_interval(time::interval(SEC30)),
            file_timer: crate::rustdesk_interval(time::interval(SEC30)),
            file_transfer: None,
            view_camera: false,
            terminal: false,
            port_forward_socket: None,
            port_forward_address: "".to_owned(),
            tx_to_cm,
            authorized: false,
            keyboard: Self::permission(keys::OPTION_ENABLE_KEYBOARD, &control_permissions),
            clipboard: Self::permission(keys::OPTION_ENABLE_CLIPBOARD, &control_permissions),
            audio: Self::permission(keys::OPTION_ENABLE_AUDIO, &control_permissions),
            // to-do: make sure is the option correct here
            file: Self::permission(keys::OPTION_ENABLE_FILE_TRANSFER, &control_permissions),
            restart: Self::permission(keys::OPTION_ENABLE_REMOTE_RESTART, &control_permissions),
            recording: Self::permission(keys::OPTION_ENABLE_RECORD_SESSION, &control_permissions),
            block_input: Self::permission(keys::OPTION_ENABLE_BLOCK_INPUT, &control_permissions),
            privacy_mode: Self::permission(keys::OPTION_ENABLE_PRIVACY_MODE, &control_permissions),
            control_permissions,
            last_test_delay: None,
            network_delay: 0,
            lock_after_session_end: false,
            show_remote_cursor: false,
            follow_remote_cursor: false,
            follow_remote_window: false,
            multi_ui_session: false,
            ip: "".to_owned(),
            disable_audio: false,
            #[cfg(any(target_os = "windows", target_os = "linux", target_os = "macos"))]
            enable_file_transfer: false,
            disable_clipboard: false,
            disable_keyboard: false,
            #[cfg(not(any(target_os = "android", target_os = "ios")))]
            show_my_cursor: false,
            tx_input,
            video_ack_required: false,
            server_audit_conn: "".to_owned(),
            server_audit_file: "".to_owned(),
            lr: Default::default(),
            peer_argb: 0u32,
            session_last_recv_time: None,
            chat_unanswered: false,
            file_transferred: false,
            #[cfg(windows)]
            portable: Default::default(),
            from_switch: false,
            audio_sender: None,
            voice_call_request_timestamp: None,
            voice_calling: false,
            options_in_login: None,
            #[cfg(not(any(target_os = "ios")))]
            pressed_modifiers: Default::default(),
            #[cfg(target_os = "linux")]
            linux_headless_handle,
            closed: false,
            #[cfg(not(any(target_os = "android", target_os = "ios")))]
            start_cm_ipc_para: Some(StartCmIpcPara {
                rx_to_cm,
                tx_from_cm,
                rx_desktop_ready,
                tx_cm_stream_ready,
            }),
            auto_disconnect_timer: None,
            authed_conn_id: None,
            file_remove_log_control: FileRemoveLogControl::new(id),
            last_supported_encoding: None,
            services_subed: false,
            delayed_read_dir: None,
            #[cfg(target_os = "macos")]
            retina: Retina::default(),
            tx_from_authed,
            printer_data: Vec::new(),
            tx_post_seq,
            cm_read_job_ids: HashSet::new(),
            terminal_service_id: "".to_owned(),
            terminal_persistent: false,
            #[cfg(not(any(target_os = "android", target_os = "ios")))]
            terminal_user_token: None,
            terminal_generic_service: None,
        };
        let addr = hbb_common::try_into_v4(addr);
        if !conn.on_open(addr).await {
            conn.closed = true;
            // sleep to ensure msg got received.
            sleep(1.).await;
            return;
        }
        #[cfg(target_os = "android")]
        start_channel(rx_to_cm, tx_from_cm);
        #[cfg(target_os = "android")]
        conn.send_permission(Permission::Keyboard, conn.keyboard)
            .await;
        #[cfg(not(target_os = "android"))]
        if !conn.keyboard {
            conn.send_permission(Permission::Keyboard, false).await;
        }
        if !conn.clipboard {
            conn.send_permission(Permission::Clipboard, false).await;
        }
        if !conn.audio {
            conn.send_permission(Permission::Audio, false).await;
        }
        if !conn.file {
            conn.send_permission(Permission::File, false).await;
        }
        if !conn.restart {
            conn.send_permission(Permission::Restart, false).await;
        }
        if !conn.recording {
            conn.send_permission(Permission::Recording, false).await;
        }
        if !conn.block_input {
            conn.send_permission(Permission::BlockInput, false).await;
        }
        if !conn.privacy_mode {
            conn.send_permission(Permission::PrivacyMode, false).await;
        }
        let mut test_delay_timer =
            crate::rustdesk_interval(time::interval_at(Instant::now(), TEST_DELAY_TIMEOUT));
        let mut last_recv_time = Instant::now();

        conn.stream.set_send_timeout(
            if conn.file_transfer.is_some() || conn.port_forward_socket.is_some() || conn.terminal {
                SEND_TIMEOUT_OTHER
            } else {
                SEND_TIMEOUT_VIDEO
            },
        );

        #[cfg(not(any(target_os = "android", target_os = "ios")))]
        std::thread::spawn(move || Self::handle_input(_rx_input, tx_cloned));
        let mut second_timer = crate::rustdesk_interval(time::interval(Duration::from_secs(1)));

        #[cfg(feature = "unix-file-copy-paste")]
        let rx_clip_holder;
        let mut rx_clip;
        let _tx_clip: mpsc::UnboundedSender<i32>;
        #[cfg(feature = "unix-file-copy-paste")]
        {
            rx_clip_holder = (
                clipboard::get_rx_cliprdr_server(id),
                crate::SimpleCallOnReturn {
                    b: true,
                    f: Box::new(move || {
                        clipboard::remove_channel_by_conn_id(id);
                    }),
                },
            );
            rx_clip = rx_clip_holder.0.lock().await;
        }
        #[cfg(not(feature = "unix-file-copy-paste"))]
        {
            (_tx_clip, rx_clip) = mpsc::unbounded_channel::<i32>();
        }

        loop {
            tokio::select! {
                // biased; // video has higher priority // causing test_delay_timer failed while transferring big file

                Some(data) = rx_from_cm.recv() => {
                    match data {
                        ipc::Data::Authorize => {
                            conn.require_2fa.take();
                            if !conn.send_logon_response_and_keep_alive().await {
                                break;
                            }
                            if conn.port_forward_socket.is_some() {
                                break;
                            }
                        }
                        ipc::Data::Close => {
                            conn.chat_unanswered = false; // seen
                            conn.file_transferred = false; //seen
                            conn.send_close_reason_no_retry("").await;
                            conn.on_close("connection manager", true).await;
                            break;
                        }
                        ipc::Data::CmErr(e) => {
                            if e != "expected" {
                                // cm closed before connection
                                conn.on_close(&format!("connection manager error: {}", e), false).await;
                                break;
                            }
                        }
                        ipc::Data::ChatMessage{text} => {
                            let mut misc = Misc::new();
                            misc.set_chat_message(ChatMessage {
                                text,
                                ..Default::default()
                            });
                            let mut msg_out = Message::new();
                            msg_out.set_misc(misc);
                            conn.send(msg_out).await;
                            conn.chat_unanswered = false;
                        }
                        ipc::Data::SwitchPermission{name, enabled} => {
                            log::info!("Change permission {} -> {}", name, enabled);
                            if &name == "keyboard" {
                                conn.keyboard = enabled;
                                conn.send_permission(Permission::Keyboard, enabled).await;
                                if let Some(s) = conn.server.upgrade() {
                                    s.write().unwrap().subscribe(
                                        super::clipboard_service::NAME,
                                        conn.inner.clone(), conn.can_sub_clipboard_service());
                                    #[cfg(feature = "unix-file-copy-paste")]
                                    s.write().unwrap().subscribe(
                                        super::clipboard_service::FILE_NAME,
                                        conn.inner.clone(),
                                        conn.can_sub_file_clipboard_service(),
                                    );
                                    s.write().unwrap().subscribe(
                                        NAME_CURSOR,
                                        conn.inner.clone(), enabled || conn.show_remote_cursor);
                                }
                            } else if &name == "clipboard" {
                                conn.clipboard = enabled;
                                conn.send_permission(Permission::Clipboard, enabled).await;
                                if let Some(s) = conn.server.upgrade() {
                                    s.write().unwrap().subscribe(
                                        super::clipboard_service::NAME,
                                        conn.inner.clone(), conn.can_sub_clipboard_service());
                                }
                            } else if &name == "audio" {
                                conn.audio = enabled;
                                conn.send_permission(Permission::Audio, enabled).await;
                                if conn.authorized {
                                    if let Some(s) = conn.server.upgrade() {
                                        if conn.is_authed_view_camera_conn() {
                                            if conn.voice_calling || !conn.audio_enabled() {
                                                s.write().unwrap().subscribe(
                                                    super::audio_service::NAME,
                                                    conn.inner.clone(), conn.audio_enabled());
                                            }
                                        } else {
                                            s.write().unwrap().subscribe(
                                                super::audio_service::NAME,
                                                conn.inner.clone(), conn.audio_enabled());
                                        }
                                    }
                                }
                            } else if &name == "file" {
                                conn.file = enabled;
                                conn.send_permission(Permission::File, enabled).await;
                                #[cfg(feature = "unix-file-copy-paste")]
                                if !enabled {
                                    conn.try_empty_file_clipboard();
                                }
                                #[cfg(feature = "unix-file-copy-paste")]
                                if let Some(s) = conn.server.upgrade() {
                                    s.write().unwrap().subscribe(
                                        super::clipboard_service::FILE_NAME,
                                        conn.inner.clone(),
                                        conn.can_sub_file_clipboard_service(),
                                    );
                                }
                            } else if &name == "restart" {
                                conn.restart = enabled;
                                conn.send_permission(Permission::Restart, enabled).await;
                            } else if &name == "recording" {
                                conn.recording = enabled;
                                conn.send_permission(Permission::Recording, enabled).await;
                            } else if &name == "block_input" {
                                conn.block_input = enabled;
                                conn.send_permission(Permission::BlockInput, enabled).await;
                            } else if &name == "privacy_mode" {
                                // Keep permission state and runtime state consistent:
                                // when revoking the permission, try to leave privacy mode first.
                                // Otherwise we could end up in an inconsistent state where
                                // permission looks disabled while privacy mode is still active.
                                if !enabled && privacy_mode::is_in_privacy_mode() {
                                    if let Some(conn_id) = privacy_mode::get_privacy_mode_conn_id() {
                                        if conn_id == conn.inner.id() {
                                            let impl_key =
                                                privacy_mode::get_cur_impl_key().unwrap_or_default();
                                            let turn_off_res =
                                                privacy_mode::turn_off_privacy(conn_id, None);
                                            match turn_off_res {
                                                Some(Ok(_)) => {
                                                    let msg_out = crate::common::make_privacy_mode_msg(
                                                        back_notification::PrivacyModeState::PrvOffByPeer,
                                                        impl_key.clone(),
                                                    );
                                                    conn.send(msg_out).await;
                                                }
                                                _ => {
                                                    let msg_out = Self::turn_off_privacy_result_to_msg(
                                                        turn_off_res,
                                                        impl_key,
                                                    );
                                                    conn.send(msg_out).await;
                                                    // Turn-off failed, so revert CM's optimistic toggle
                                                    // and keep the previous permission value.
                                                    conn.send_to_cm(ipc::Data::SwitchPermission {
                                                        name: "privacy_mode".to_owned(),
                                                        enabled: conn.privacy_mode,
                                                    });
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                                conn.privacy_mode = enabled;
                                conn.send_permission(Permission::PrivacyMode, enabled).await;
                            }
                        }
                        ipc::Data::RawMessage(bytes) => {
                            allow_err!(conn.stream.send_raw(bytes).await);
                        }
                        #[cfg(target_os = "windows")]
                        ipc::Data::ClipboardFile(clip) => {
                            if !conn.is_remote() {
                                continue;
                            }
                            match clip {
                                clipboard::ClipboardFile::Files { files } => {
                                    let files = files.into_iter().map(|(f, s)| {
                                        (f, s as i64)
                                    }).collect::<Vec<_>>();
                                    conn.post_file_audit(
                                        FileAuditType::RemoteSend,
                                        "",
                                        files,
                                        json!({}),
                                    );
                                }
                                _ => {
                                    allow_err!(conn.stream.send(&clip_2_msg(clip)).await);
                                }
                            }
                        }
                        ipc::Data::PrivacyModeState((_, state, impl_key)) => {
                            let msg_out = match state {
                                privacy_mode::PrivacyModeState::OffSucceeded => {
                                    crate::common::make_privacy_mode_msg(
                                        back_notification::PrivacyModeState::PrvOffSucceeded,
                                        impl_key,
                                    )
                                }
                                privacy_mode::PrivacyModeState::OffByPeer => {
                                    crate::common::make_privacy_mode_msg(
                                        back_notification::PrivacyModeState::PrvOffByPeer,
                                        impl_key,
                                    )
                                }
                                privacy_mode::PrivacyModeState::OffUnknown => {
                                     crate::common::make_privacy_mode_msg(
                                        back_notification::PrivacyModeState::PrvOffUnknown,
                                        impl_key,
                                    )
                                }
                            };
                            conn.send(msg_out).await;
                        }
                        #[cfg(windows)]
                        ipc::Data::DataPortableService(ipc::DataPortableService::RequestStart) => {
                            if let Err(e) = portable_client::start_portable_service(portable_client::StartPara::Direct) {
                                log::error!("Failed to start portable service from cm: {:?}", e);
                            }
                        }
                        #[cfg(feature = "flutter")]
                        #[cfg(not(any(target_os = "android", target_os = "ios")))]
                        ipc::Data::SwitchSidesBack => {
                            let mut misc = Misc::new();
                            misc.set_switch_back(SwitchBack::default());
                            let mut msg = Message::new();
                            msg.set_misc(misc);
                            conn.send(msg).await;
                        }
                        ipc::Data::VoiceCallResponse(accepted) => {
                            conn.handle_voice_call(accepted).await;
                        }
                        ipc::Data::CloseVoiceCall(_reason) => {
                            log::debug!("Close the voice call from the ipc.");
                            conn.close_voice_call().await;
                            // Notify the peer that we closed the voice call.
                            let msg = new_voice_call_request(false);
                            conn.send(msg).await;
                        }
                        ipc::Data::ReadJobInitResult { id, file_num, include_hidden, conn_id, result } => {
                            if conn_id == conn.inner.id() {
                                conn.handle_read_job_init_result(id, file_num, include_hidden, result).await;
                            }
                        }
                        ipc::Data::FileBlockFromCM { id, file_num, data, compressed, conn_id } => {
                            if conn_id == conn.inner.id() {
                                conn.handle_file_block_from_cm(id, file_num, data, compressed).await;
                            }
                        }
                        ipc::Data::FileReadDone { id, file_num, conn_id } => {
                            if conn_id == conn.inner.id() {
                                conn.handle_file_read_done(id, file_num).await;
                            }
                        }
                        ipc::Data::FileReadError { id, file_num, err, conn_id } => {
                            if conn_id == conn.inner.id() {
                                conn.handle_file_read_error(id, file_num, err).await;
                            }
                        }
                        ipc::Data::FileDigestFromCM { id, file_num, last_modified, file_size, is_resume, conn_id } => {
                            if conn_id == conn.inner.id() {
