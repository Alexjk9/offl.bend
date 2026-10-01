const { app, BrowserWindow, ipcMain, screen } = require('electron');
const { spawn } = require('child_process');
const net = require('net');
const path = require('path');
const koffi = require('koffi');

const root = path.resolve(__dirname, '..');
const exe = process.env.EDITOR_EXE || path.join(root, 'src', 'editor.exe');
const port = Number(process.env.PT_PORT || 7777);

const user32 = koffi.load('user32.dll');
const RECT = koffi.struct('RECT', { left: 'long', top: 'long', right: 'long', bottom: 'long' });
const POINT = koffi.struct('POINT', { x: 'long', y: 'long' });
const EnumWindowsProc = koffi.proto('int __stdcall EnumWindowsProc(void *hwnd, intptr_t lParam)');
const EnumWindows = user32.func('int __stdcall EnumWindows(EnumWindowsProc *cb, intptr_t lParam)');
const GetWindowThreadProcessId = user32.func('uint32_t __stdcall GetWindowThreadProcessId(void *hwnd, _Out_ uint32_t *pid)');
const IsWindowVisible = user32.func('int __stdcall IsWindowVisible(void *hwnd)');
const IsWindow = user32.func('int __stdcall IsWindow(void *hwnd)');
const IsIconic = user32.func('int __stdcall IsIconic(void *hwnd)');
const GetClientRect = user32.func('int __stdcall GetClientRect(void *hwnd, _Out_ RECT *rect)');
const ClientToScreen = user32.func('int __stdcall ClientToScreen(void *hwnd, _Inout_ POINT *pt)');
const GetForegroundWindow = user32.func('void *__stdcall GetForegroundWindow()');

let win = null;
let sock = null;
let child = null;
let hwnd = null;

function log(msg) {
  console.log(`ui: ${msg}`);
}

function state(s) {
  if (win && !win.isDestroyed() && !win.webContents.isLoading()) {
    win.webContents.send('state', s);
  }
}

function connect() {
  const s = net.connect(port, '127.0.0.1');
  s.on('connect', () => {
    sock = s;
    log(`connected to the editor on port ${port}`);
    state('connected');
  });
  s.on('error', (e) => {
    if (sock === s) {
      log(`socket error: ${e.message}`);
      sock = null;
    } else {
      setTimeout(connect, 500);
    }
  });
  s.on('close', () => {
    if (sock === s) {
      sock = null;
      log('editor closed the connection');
    }
    state('disconnected');
  });
}

function startEditor() {
  log(`starting ${exe}`);
  child = spawn(exe, [], {
    cwd: root,
    stdio: 'inherit',
    env: { ...process.env, PT_PORT: String(port) },
  });
  child.on('exit', (code) => {
    log(`editor exited (${code})`);
    app.quit();
  });
  child.on('error', (e) => {
    log(`could not start ${exe}: ${e.message}`);
    app.quit();
  });
}

function pidOf(h) {
  const pid = [0];
  GetWindowThreadProcessId(h, pid);
  return pid[0];
}

function findEditorWindow() {
  let found = null;
  EnumWindows((h) => {
    if (pidOf(h) === child.pid && IsWindowVisible(h)) {
      found = h;
      return 0;
    }
    return 1;
  }, 0);
  return found;
}

function editorBounds() {
  const rc = {};
  const pt = { x: 0, y: 0 };
  if (!GetClientRect(hwnd, rc) || !ClientToScreen(hwnd, pt)) return null;
  return screen.screenToDipRect(null, {
    x: pt.x,
    y: pt.y,
    width: rc.right - rc.left,
    height: rc.bottom - rc.top,
  });
}

function inFront() {
  const fg = GetForegroundWindow();
  if (!fg) return false;
  const pid = pidOf(fg);
  return pid === child.pid || pid === process.pid;
}

function track() {
  if (!child || !win || win.isDestroyed()) return;
  if (hwnd && !IsWindow(hwnd)) hwnd = null;
  if (!hwnd) hwnd = findEditorWindow();
  if (!hwnd) return;
  const b = editorBounds();
  if (!b || IsIconic(hwnd) || !inFront()) {
    if (win.isVisible()) win.hide();
    return;
  }
  const cur = win.getBounds();
  if (cur.x !== b.x || cur.y !== b.y || cur.width !== b.width || cur.height !== b.height) {
    win.setBounds(b);
  }
  if (!win.isVisible()) win.showInactive();
}

function createOverlay() {
  win = new BrowserWindow({
    width: 1024,
    height: 1024,
    show: false,
    frame: false,
    transparent: true,
    alwaysOnTop: true,
    focusable: true,
    skipTaskbar: true,
    hasShadow: false,
    webPreferences: {
      preload: path.join(__dirname, 'preload.js'),
    },
  });
  win.setAlwaysOnTop(true, 'screen-saver');
  win.webContents.on('did-finish-load', () => {
    state(sock ? 'connected' : 'disconnected');
  });
  win.webContents.on('preload-error', (_e, p, err) => {
    log(`preload failed (${p}): ${err.message}`);
  });
  win.loadFile(path.join(__dirname, 'overlay.html'));
}

function send(line) {
  if (sock) {
    sock.write(`${line}\n`);
  } else {
    log(`${line} dropped: not connected`);
  }
}

ipcMain.on('mode', (_e, n) => {
  log(`mode ${n}`);
  send(`mode ${n}`);
});

ipcMain.on('pause', () => {
  log('pause');
  send('pause');
});

ipcMain.on('walk', (_e, f, s, u) => {
  send(`walk ${f.toFixed(4)} ${s.toFixed(4)} ${u.toFixed(4)}`);
});

ipcMain.on('turn', (_e, yaw, pitch) => {
  send(`turn ${yaw.toFixed(4)} ${pitch.toFixed(4)}`);
});

app.whenReady().then(() => {
  createOverlay();
  startEditor();
  connect();
  setInterval(track, 33);
});

app.on('window-all-closed', () => {
  if (child) child.kill();
  app.quit();
});

app.on('quit', () => {
  if (child) child.kill();
});
