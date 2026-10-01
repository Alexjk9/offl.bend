const { contextBridge, ipcRenderer } = require('electron');

contextBridge.exposeInMainWorld('ui', {
  mode: (n) => ipcRenderer.send('mode', n),
  pause: () => ipcRenderer.send('pause'),
  walk: (f, s, u) => ipcRenderer.send('walk', f, s, u),
  turn: (yaw, pitch) => ipcRenderer.send('turn', yaw, pitch),
  onState: (cb) => ipcRenderer.on('state', (_e, s) => cb(s)),
});
