import { existsSync, writeFileSync, mkdtempSync, rmSync } from "node:fs";
import { spawn } from "node:child_process";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";

const BROWSERS = [
  process.env.BROWSER,
  "C:\\Program Files (x86)\\Microsoft\\Edge\\Application\\msedge.exe",
  "C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe",
  "C:\\Program Files (x86)\\Google\\Chrome\\Application\\chrome.exe",
  "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
  "/Applications/Microsoft Edge.app/Contents/MacOS/Microsoft Edge",
  "google-chrome",
  "chromium",
  "microsoft-edge",
];

const PAGE = `<!doctype html><script>
function spread(v) {
  v = (v | (v << 8)) & 0x00ff00ff;
  v = (v | (v << 4)) & 0x0f0f0f0f;
  v = (v | (v << 2)) & 0x33333333;
  v = (v | (v << 1)) & 0x55555555;
  return v;
}
async function convert(url, size) {
  const bitmap = await createImageBitmap(await (await fetch(url)).blob());
  const n = size || bitmap.width;
  if (!size && (bitmap.width !== bitmap.height || n < 2 || (n & (n - 1)) !== 0)) {
    return { error: "not a power-of-two square: " + bitmap.width + "x" + bitmap.height };
  }
  const canvas = new OffscreenCanvas(n, n);
  const ctx = canvas.getContext("2d");
  ctx.drawImage(bitmap, 0, 0, n, n);
  const px = ctx.getImageData(0, 0, n, n).data;
  const words = new Uint32Array(n * n);
  for (let y = 0; y < n; y += 1) {
    for (let x = 0; x < n; x += 1) {
      const i = (y * n + x) * 4;
      words[spread(x) | (spread(y) << 1)] = (px[i] << 16) | (px[i + 1] << 8) | px[i + 2];
    }
  }
  const bytes = new Uint8Array(words.buffer);
  let text = "";
  for (let i = 0; i < bytes.length; i += 8192) {
    text += String.fromCharCode.apply(null, bytes.subarray(i, i + 8192));
  }
  return { width: bitmap.width, height: bitmap.height, size: n, data: btoa(text) };
}
</script>`;

function fail(message) {
  console.error("img2tex: " + message);
  process.exit(1);
}

function browser() {
  for (const candidate of BROWSERS) {
    if (!candidate) continue;
    if (existsSync(candidate)) return candidate;
    const found = Bun.which(candidate);
    if (found) return found;
  }
  fail("no Chrome or Edge found; set BROWSER to the executable");
}

function launch(exe, profile) {
  const proc = spawn(exe, [
    "--headless=new", "--remote-debugging-port=0", "--disable-gpu", "--no-first-run",
    "--no-default-browser-check", "--user-data-dir=" + profile, "about:blank",
  ]);
  const endpoint = new Promise((ok, no) => {
    let text = "";
    proc.stderr.on("data", (chunk) => {
      text += chunk;
      const m = /DevTools listening on (ws:\/\/[^\s]+)/.exec(text);
      if (m) ok(m[1]);
    });
    proc.on("exit", (code) => no(new Error("the browser exited with " + code + "\n" + text)));
  });
  return { proc, endpoint };
}

async function attach(endpoint) {
  const port = new URL(endpoint).port;
  const targets = await (await fetch("http://127.0.0.1:" + port + "/json")).json();
  const page = targets.find((t) => t.type === "page");
  if (!page) fail("the browser opened no page");
  const socket = new WebSocket(page.webSocketDebuggerUrl);
  await new Promise((ok, no) => { socket.onopen = ok; socket.onerror = no; });
  const pending = new Map();
  const events = new Map();
  let next = 1;
  socket.onmessage = (m) => {
    const msg = JSON.parse(m.data);
    if (msg.id !== undefined) {
      const p = pending.get(msg.id);
      pending.delete(msg.id);
      msg.error ? p.no(new Error(msg.error.message)) : p.ok(msg.result);
    } else if (events.has(msg.method)) {
      events.get(msg.method)();
      events.delete(msg.method);
    }
  };
  return {
    send(method, params = {}) {
      const id = next++;
      socket.send(JSON.stringify({ id, method, params }));
      return new Promise((ok, no) => pending.set(id, { ok, no }));
    },
    once(method) {
      return new Promise((ok) => events.set(method, ok));
    },
    close() {
      socket.close();
    },
  };
}

function serve(files) {
  return Bun.serve({
    port: 0,
    hostname: "127.0.0.1",
    fetch(req) {
      const path = new URL(req.url).pathname;
      if (path === "/page") return new Response(PAGE, { headers: { "content-type": "text/html" } });
      const m = /^\/asset\/(\d+)$/.exec(path);
      if (m && files[m[1]]) return new Response(Bun.file(files[m[1]]));
      return new Response("not found", { status: 404 });
    },
  });
}

function write(output, result) {
  const words = Buffer.from(result.data, "base64");
  const out = Buffer.alloc(4 + words.length);
  out.writeUInt32LE(Math.log2(result.size) - 1, 0);
  words.copy(out, 4);
  writeFileSync(output, out);
}

async function main(args) {
  let size = 0;
  const files = [];
  for (let i = 0; i < args.length; i += 1) {
    if (args[i] === "--size") {
      size = Number(args[++i]);
      if (!(size >= 2) || (size & (size - 1)) !== 0) fail("--size takes a power of two of at least 2");
    } else {
      files.push(resolve(args[i]));
    }
  }
  if (files.length === 0) fail("usage: bun tools/img2tex.js [--size N] image...");
  const profile = mkdtempSync(join(tmpdir(), "img2tex-"));
  const server = serve(files);
  const { proc, endpoint } = launch(browser(), profile);
  let failed = 0;
  try {
    const cdp = await attach(await endpoint);
    await cdp.send("Page.enable");
    const loaded = cdp.once("Page.loadEventFired");
    await cdp.send("Page.navigate", { url: "http://127.0.0.1:" + server.port + "/page" });
    await loaded;
    for (let i = 0; i < files.length; i += 1) {
      const output = files[i].replace(/\.[^./\\]+$/, "") + ".tex";
      const { result } = await cdp.send("Runtime.evaluate", {
        expression: "convert('/asset/" + i + "', " + size + ")",
        awaitPromise: true,
        returnByValue: true,
      });
      if (result.value.error) {
        console.error(files[i] + ": " + result.value.error);
        failed += 1;
        continue;
      }
      write(output, result.value);
      console.log(output + ": " + result.value.width + "x" + result.value.height + " -> " + result.value.size
        + ", " + (Math.log2(result.value.size) - 1) + " levels");
    }
    cdp.close();
  } finally {
    server.stop(true);
    await stop(proc);
    await remove(profile);
  }
  process.exit(failed === 0 ? 0 : 1);
}

function stop(proc) {
  return new Promise((ok) => {
    if (proc.exitCode !== null) return ok();
    const timer = setTimeout(() => { proc.kill("SIGKILL"); ok(); }, 5000);
    proc.once("exit", () => { clearTimeout(timer); ok(); });
    proc.kill();
  });
}

async function remove(dir) {
  for (let attempt = 0; attempt < 20; attempt += 1) {
    try {
      rmSync(dir, { recursive: true, force: true });
      return;
    } catch (e) {
      if (e.code !== "EBUSY" && e.code !== "EPERM" && e.code !== "ENOTEMPTY") throw e;
      await new Promise((ok) => setTimeout(ok, 250));
    }
  }
  console.error("img2tex: warning: could not remove the temporary profile " + dir);
}

main(process.argv.slice(2));
