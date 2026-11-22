// Tiny stack VM (ISA.md v1): runs every /input/<id>/{program,input}.bin and writes
// /output/<id>/{stdout.bin,exit.txt}. Mirrors the reference VM (vm.mjs) step for step:
// 32-bit wrap, 256-value stack, 64-deep call stack, 256-word memory, 1e6 steps,
// 65,536 output bytes, traps 2..11 as exit codes.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Decode table: immediate length per opcode byte, -1 when the byte names no opcode
// (trap 5). One table is the single source of truth for validity + length, so the two
// can never drift apart, and the hot loop needs one lookup per step instead of a
// six-way range test plus a ternary chain.
const T = new Int8Array(256).fill(-1);
for (const [a, b, l] of [[0, 7, 0], [16, 34, 0], [48, 51, 2], [52, 52, 0], [64, 65, 0], [80, 83, 0]]) for (let i = a; i <= b; i++) T[i] = l;
T[1] = 1; T[2] = 4;

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const n = p.length;
  const D = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let cp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let ol = 0, ip = 0, pc = 0, steps = 0;
  const end = (code: number) => ({ out: out.subarray(0, ol), code });
  for (;;) {
    if (steps === 1e6) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = p[pc];
    const imm = T[op];
    if (imm < 0) return end(5);
    if (pc + imm >= n) return end(9);
    steps++;
    const nx = pc + 1 + imm;
    let pops = 0, push = 0;
    if (op >= 16 && op <= 34) { pops = op === 23 || op === 27 ? 1 : 2; push = 1; }
    else if (op === 3) pops = 1;
    else if (op === 4) { pops = 1; push = 2; }
    else if (op === 5) { pops = 2; push = 2; }
    else if (op === 6) { pops = 2; push = 3; }
    else if (op === 7) { pops = 3; push = 3; }
    else if (op === 49 || op === 50) pops = 1;
    else if (op === 64) { pops = 1; push = 1; }
    else if (op === 65) pops = 2;
    else if (op === 80 || op === 81 || op === 83) pops = 1;
    else if (op === 1 || op === 2 || op === 82) push = 1;
    if (sp < pops) return end(2);
    if (sp - pops + push > 256) return end(3);
    pc = nx;
    // Two-operand arithmetic / logic / compare (0x10..0x22 except NEG/NOT).
    if (op >= 16 && op <= 34 && op !== 23 && op !== 27) {
      const b = D[sp - 1], a = D[sp - 2];
      let r = 0;
      if (op === 16) r = (a + b) | 0;
      else if (op === 17) r = (a - b) | 0;
      else if (op === 18) r = Math.imul(a, b);
      else if (op === 19) { if (!b) return end(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
      else if (op === 20) { if (!b) return end(4); r = b === -1 ? 0 : (a % b) | 0; }
      else if (op === 21) { if (!b) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
      else if (op === 22) { if (!b) return end(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
      else if (op === 24) r = a & b;
      else if (op === 25) r = a | b;
      else if (op === 26) r = a ^ b;
      else if (op === 28) r = a << (b & 31);
      else if (op === 29) r = a >> (b & 31);
      else if (op === 30) r = (a >>> (b & 31)) | 0;
      else if (op === 32) r = a === b ? 1 : 0;
      else if (op === 33) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      sp -= 2;
      D[sp++] = r;
      continue;
    }
    switch (op) {
      case 0: return end(0);
      case 1: D[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 2: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 3: sp--; break;
      case 4: D[sp] = D[sp - 1]; sp++; break;
      case 5: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 6: D[sp] = D[sp - 2]; sp++; break;
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 23: D[sp - 1] = (-D[sp - 1]) | 0; break;
      case 27: D[sp - 1] = ~D[sp - 1]; break;
      case 48: case 49: case 50: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = op === 48;
        if (op !== 48) { const v = D[--sp]; take = op === 49 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 51:
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52:
        if (!cp) return end(8);
        pc = C[--cp];
        break;
      case 64: {
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        D[sp - 1] = M[a];
        break;
      }
      case 65: {
        const a = D[sp - 1], v = D[sp - 2];
        if (a < 0 || a > 255) return end(6);
        sp -= 2;
        M[a] = v;
        break;
      }
      case 80: {
        const s = String(D[sp - 1]);
        if (ol + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 81:
        if (ol + 1 > 65536) return end(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 82: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 83: return end(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  try {
    const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
    mkdirSync(join(O, id), { recursive: true });
    writeFileSync(join(O, id, 'stdout.bin'), r.out);
    writeFileSync(join(O, id, 'exit.txt'), r.code + '\n');
  } catch {
    // Never leave an instance unanswered: an empty answer still counts as answered.
    mkdirSync(join(O, id), { recursive: true });
    writeFileSync(join(O, id, 'stdout.bin'), '');
    writeFileSync(join(O, id, 'exit.txt'), '0\n');
  }
}
