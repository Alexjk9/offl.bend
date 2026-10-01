// P3 PPM on stdin to a PNG at argv[2].
const fs = require("fs");
const zlib = require("zlib");

const out = process.argv[2];
const tok = fs.readFileSync(0, "utf8").split(/\s+/).filter(Boolean);
if (tok[0] !== "P3") {
  console.error("ppm2png: not a P3 file");
  process.exit(1);
}
const w = Number(tok[1]);
const h = Number(tok[2]);
const row = w * 3 + 1;
const raw = Buffer.alloc(row * h);
let k = 4;
for (let y = 0; y < h; y += 1) {
  raw[y * row] = 0;
  for (let x = 1; x < row; x += 1) {
    raw[y * row + x] = Number(tok[k++]);
  }
}

const table = new Uint32Array(256);
for (let n = 0; n < 256; n += 1) {
  let c = n;
  for (let i = 0; i < 8; i += 1) {
    c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
  }
  table[n] = c >>> 0;
}
function crc32(buf) {
  let c = 0xffffffff;
  for (const b of buf) {
    c = table[(c ^ b) & 0xff] ^ (c >>> 8);
  }
  return (c ^ 0xffffffff) >>> 0;
}
function chunk(type, data) {
  const len = Buffer.alloc(4);
  len.writeUInt32BE(data.length);
  const body = Buffer.concat([Buffer.from(type, "ascii"), data]);
  const crc = Buffer.alloc(4);
  crc.writeUInt32BE(crc32(body));
  return Buffer.concat([len, body, crc]);
}

const ihdr = Buffer.alloc(13);
ihdr.writeUInt32BE(w, 0);
ihdr.writeUInt32BE(h, 4);
ihdr[8] = 8;
ihdr[9] = 2;
ihdr[10] = 0;
ihdr[11] = 0;
ihdr[12] = 0;

fs.writeFileSync(out, Buffer.concat([
  Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]),
  chunk("IHDR", ihdr),
  chunk("IDAT", zlib.deflateSync(raw)),
  chunk("IEND", Buffer.alloc(0)),
]));
