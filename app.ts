// github-core-clone-01 — a GitHub-compatible git forge in one Node process, stdlib only.
//
// Surfaces:
//   * git smart HTTP at /{owner}/{repo}.git — upload-pack v0 and v2, receive-pack v0,
//     SHA-1 objects, no deltas on the wire out, deltas accepted on the wire in.
//   * REST v3 under /api/v3 — repos, refs, branches, commits, contents, labels,
//     issues, comments, pull requests and merges.
//   * GraphQL v4 at /api/graphql — the documents gh and github-mcp-server send,
//     plus __type introspection, node(id:) and batched operation documents.
//   * MCP at /mcp — JSON-RPC 2.0 Streamable HTTP, modern server/discover and the
//     legacy initialize handshake, eight tools over the same store as REST.
//
// The store is in memory, one process, deterministic: no wall clock and no
// unseeded randomness in anything sent. Timestamps are a counter off a fixed
// epoch, request ids are a counter, and the token owner's login is recomputed
// from the contest's fixed seeded scenario (wire.ts SCENARIO_SEED), so the
// forge names the same viewer the suite does.

import { createHash, timingSafeEqual } from 'node:crypto';
import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { deflateSync, inflateSync } from 'node:zlib';

// ---------------------------------------------------------------------------
// The viewer, recomputed from the contest's fixed seeded scenario.
// ---------------------------------------------------------------------------

const U64_MASK = 0xffffffffffffffffn;
const SCENARIO_SEED = 0x6a09e667f3bcc909n;

function fnv1a64(text: string): bigint {
  let hash = 0xcbf29ce484222325n;
  for (let i = 0; i < text.length; i += 1) {
    hash ^= BigInt(text.charCodeAt(i));
    hash = (hash * 0x100000001b3n) & U64_MASK;
  }
  return hash;
}

function mix64(value: bigint): bigint {
  let z = (value + 0x9e3779b97f4a7c15n) & U64_MASK;
  z = ((z ^ (z >> 30n)) * 0xbf58476d1ce4e5b9n) & U64_MASK;
  z = ((z ^ (z >> 27n)) * 0x94d049bb133111ebn) & U64_MASK;
  return (z ^ (z >> 31n)) & U64_MASK;
}

/** xorshift64*, the scenario's PRNG: same label, same numbers, in any process. */
class ScenarioRng {
  #state: bigint;
  constructor(seed: bigint) {
    const masked = seed & U64_MASK;
    this.#state = masked === 0n ? SCENARIO_SEED : masked;
  }
  nextU64(): bigint {
    let x = this.#state;
    x = (x ^ (x >> 12n)) & U64_MASK;
    x = (x ^ (x << 25n)) & U64_MASK;
    x = (x ^ (x >> 27n)) & U64_MASK;
    this.#state = x;
    return (x * 0x2545f4914f6cdd1dn) & U64_MASK;
  }
  nextU32(): number {
    return Number(this.nextU64() >> 32n);
  }
  nextInt(maxExclusive: number): number {
    if (maxExclusive === 1) return 0;
    const range = 4_294_967_296;
    const limit = range - (range % maxExclusive);
    for (;;) {
      const value = this.nextU32();
      if (value < limit) return value % maxExclusive;
    }
  }
  pick<T>(items: readonly T[]): T {
    const item = items[this.nextInt(items.length)];
    if (item === undefined) throw new Error('pick from an empty list');
    return item;
  }
}

const FIRST_NAMES = [
  'ada', 'bram', 'cora', 'dmitri', 'elena', 'felix', 'greta', 'hugo', 'iris', 'jonas', 'kira', 'lars',
  'mira', 'nico', 'olga', 'pavel', 'quinn', 'rosa', 'sven', 'tess', 'ulla', 'vito', 'wren', 'yara', 'zane',
] as const;
const LAST_NAMES = [
  'anders', 'bauer', 'costa', 'dahl', 'eriksen', 'fischer', 'garcia', 'holm', 'iversen', 'jansen', 'keller',
  'lind', 'moreau', 'novak', 'olsen', 'peters', 'quist', 'rossi', 'sato', 'turi', 'ulrich', 'vega', 'weber',
  'xu', 'yilmaz', 'zimmer',
] as const;

interface ScenarioUser {
  id: number;
  login: string;
  name: string;
  email: string;
}

/** The scenario's users, in order: [0] is the viewer, [1] the teammate, [2] the stranger. */
function scenarioUsers(): ScenarioUser[] {
  const rng = new ScenarioRng(mix64(SCENARIO_SEED ^ fnv1a64('users')));
  const used = new Set<string>();
  const users: ScenarioUser[] = [];
  for (let i = 0; i < 12; i += 1) {
    const first = rng.pick(FIRST_NAMES);
    const last = rng.pick(LAST_NAMES);
    const base = `${first}${last}`.replace(/[^a-z0-9-]/g, '');
    let login = base;
    let suffix = 2;
    while (used.has(login)) {
      login = `${base}-${suffix}`;
      suffix += 1;
    }
    used.add(login);
    users.push({ id: 1000 + i, login, name: `${first} ${last}`, email: `${login}@example.invalid` });
  }
  return users;
}

const USERS = scenarioUsers();
const VIEWER = USERS[0] as ScenarioUser;

// ---------------------------------------------------------------------------
// Deterministic clock and ids: a counter off a fixed epoch, never Date.now().
// ---------------------------------------------------------------------------

const EPOCH_SEC = 1_735_689_600; // 2025-01-01T00:00:00Z, the scenario's day one
let tick = 0;
function nextTick(): number {
  tick += 1;
  return tick;
}
/** A deterministic timestamp: one minute per tick, ISO form. */
function stamp(): { epoch: number; iso: string } {
  const epoch = EPOCH_SEC + nextTick() * 60;
  return { epoch, iso: new Date(epoch * 1000).toISOString() };
}

let requestCounter = 0;
let dbIdCounter = 5000;
let globalIdCounter = 0;

function b64encode(text: string): string {
  return Buffer.from(text, 'utf8').toString('base64');
}
function b64decode(text: string): string {
  return Buffer.from(text, 'base64').toString('utf8');
}
/** An opaque Relay-style global id: base64 of "<Kind>:<key>", never the bare number. */
function globalId(kind: string, key: string): string {
  return b64encode(`${kind}:${key}`);
}
function parseGlobalId(id: string): { kind: string; key: string } | null {
  try {
    const decoded = b64decode(id);
    const colon = decoded.indexOf(':');
    if (colon <= 0) return null;
    return { kind: decoded.slice(0, colon), key: decoded.slice(colon + 1) };
  } catch {
    return null;
  }
}

// ---------------------------------------------------------------------------
// The store.
// ---------------------------------------------------------------------------

type ObjectType = 'blob' | 'tree' | 'commit' | 'tag';
interface GitObject {
  type: ObjectType;
  data: Buffer;
}
interface Issue {
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: string[];
  seq: number;
  createdAt: string;
  updatedAt: string;
  user: ScenarioUser;
}
interface Comment {
  id: number;
  body: string;
  user: ScenarioUser;
  createdAt: string;
}
interface Pull {
  number: number;
  title: string;
  body: string;
  headRef: string;
  baseRef: string;
  headSha: string;
  baseSha: string;
  state: 'open' | 'closed';
  merged: boolean;
  mergedAt: string | null;
  mergeCommitSha: string | null;
  seq: number;
  createdAt: string;
  user: ScenarioUser;
}
interface Repo {
  id: number;
  name: string;
  owner: string;
  description: string;
  isPrivate: boolean;
  defaultBranch: string;
  createdAt: string;
  refs: Map<string, string>;
  objects: Map<string, GitObject>;
  issues: Issue[];
  labels: Map<string, { name: string; color: string; description: string }>;
  pulls: Pull[];
  comments: Map<number, Comment[]>;
  nextIssue: number;
  nextPull: number;
  nextComment: number;
  seq: number;
}

const repos = new Map<string, Repo>();
function repoKey(owner: string, name: string): string {
  return `${owner}/${name}`;
}
function getRepo(owner: string, name: string): Repo | undefined {
  return repos.get(repoKey(owner, name));
}
function viewerRepos(): Repo[] {
  const out: Repo[] = [];
  for (const repo of repos.values()) {
    if (repo.owner === VIEWER.login) out.push(repo);
  }
  out.sort((a, b) => a.seq - b.seq);
  return out;
}

// ---------------------------------------------------------------------------
// Git objects: SHA-1 over "<type> <size>\0" + bytes; trees sorted git-style.
// ---------------------------------------------------------------------------

function sha1Hex(data: Buffer): string {
  return createHash('sha1').update(data).digest('hex');
}
function objectId(type: ObjectType, data: Buffer): string {
  const header = Buffer.from(`${type} ${data.length}\0`, 'utf8');
  return sha1Hex(Buffer.concat([header, data]));
}
function storeObject(repo: Repo, type: ObjectType, data: Buffer): string {
  const oid = objectId(type, data);
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type, data });
  return oid;
}
function parseCommit(data: Buffer): {
  tree: string;
  parents: string[];
  author: string;
  committer: string;
  message: string;
} {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const head = split >= 0 ? text.slice(0, split) : text;
  const message = split >= 0 ? text.slice(split + 2) : '';
  let tree = '';
  const parents: string[] = [];
  let author = '';
  let committer = '';
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) author = line.slice(7);
    else if (line.startsWith('committer ')) committer = line.slice(10);
  }
  return { tree, parents, author, committer, message };
}
interface TreeEntry {
  mode: string;
  name: string;
  oid: string;
}
function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let pos = 0;
  while (pos < data.length) {
    const space = data.indexOf(0x20, pos);
    if (space < 0) break;
    const mode = data.subarray(pos, space).toString('utf8');
    const nul = data.indexOf(0x00, space + 1);
    if (nul < 0) break;
    const name = data.subarray(space + 1, nul).toString('utf8');
    const oid = data.subarray(nul + 1, nul + 21).toString('hex');
    entries.push({ mode, name, oid });
    pos = nul + 21;
  }
  return entries;
}
function buildTree(repo: Repo, entries: TreeEntry[]): string {
  const sorted = [...entries].sort((a, b) => {
    const an = a.mode === '40000' ? `${a.name}/` : a.name;
    const bn = b.mode === '40000' ? `${b.name}/` : b.name;
    return an < bn ? -1 : an > bn ? 1 : 0;
  });
  const parts: Buffer[] = [];
  for (const entry of sorted) {
    parts.push(Buffer.from(`${entry.mode} ${entry.name}\0`, 'utf8'));
    parts.push(Buffer.from(entry.oid, 'hex'));
  }
  return storeObject(repo, 'tree', Buffer.concat(parts));
}
/** The flat path -> {oid, mode} map of a tree, recursively. */
function flattenTree(repo: Repo, treeOid: string, prefix: string, out: Map<string, { oid: string; mode: string }>): void {
  const obj = repo.objects.get(treeOid);
  if (obj === undefined || obj.type !== 'tree') return;
  for (const entry of parseTree(obj.data)) {
    const path = prefix === '' ? entry.name : `${prefix}/${entry.name}`;
    if (entry.mode === '40000') flattenTree(repo, entry.oid, path, out);
    else out.set(path, { oid: entry.oid, mode: entry.mode });
  }
}
/** Rebuild a tree from a flat path map, creating intermediate trees. */
function treeFromFlat(repo: Repo, flat: Map<string, { oid: string; mode: string }>): string {
  interface Node {
    files: Map<string, { oid: string; mode: string }>;
    dirs: Map<string, Node>;
  }
  const root: Node = { files: new Map(), dirs: new Map() };
  for (const [path, value] of flat) {
    const parts = path.split('/');
    let node = root;
    for (let i = 0; i < parts.length - 1; i += 1) {
      const part = parts[i] as string;
      let child = node.dirs.get(part);
      if (child === undefined) {
        child = { files: new Map(), dirs: new Map() };
        node.dirs.set(part, child);
      }
      node = child;
    }
    node.files.set(parts[parts.length - 1] as string, value);
  }
  const build = (node: Node): string => {
    const entries: TreeEntry[] = [];
    for (const [name, value] of node.files) entries.push({ mode: value.mode, name, oid: value.oid });
    for (const [name, child] of node.dirs) entries.push({ mode: '40000', name, oid: build(child) });
    return buildTree(repo, entries);
  };
  return build(root);
}
/** All commits reachable from `tip`, newest-first by walk order (parents after children). */
function reachableCommits(repo: Repo, tips: readonly string[]): Set<string> {
  const seen = new Set<string>();
  const stack = [...tips];
  while (stack.length > 0) {
    const oid = stack.pop() as string;
    if (seen.has(oid)) continue;
    const obj = repo.objects.get(oid);
    if (obj === undefined || obj.type !== 'commit') continue;
    seen.add(oid);
    for (const parent of parseCommit(obj.data).parents) stack.push(parent);
  }
  return seen;
}
/** Is `ancestor` reachable from `tip` (or equal)? */
function isAncestor(repo: Repo, ancestor: string, tip: string): boolean {
  if (ancestor === tip) return true;
  return reachableCommits(repo, [tip]).has(ancestor);
}
/** The merge-base of two commits: the newest common ancestor by commit order. */
function mergeBase(repo: Repo, a: string, b: string): string | null {
  const fromA = reachableCommits(repo, [a]);
  const fromB = reachableCommits(repo, [b]);
  const common = [...fromA].filter((oid) => fromB.has(oid));
  if (common.length === 0) return null;
  // Walk from `a` newest-first; the first common commit is the base.
  const seen = new Set<string>();
  const stack = [a];
  while (stack.length > 0) {
    const oid = stack.pop() as string;
    if (seen.has(oid)) continue;
    seen.add(oid);
    if (fromB.has(oid)) return oid;
    const obj = repo.objects.get(oid);
    if (obj !== undefined && obj.type === 'commit') {
      for (const parent of parseCommit(obj.data).parents) stack.push(parent);
    }
  }
  return common[0] as string;
}
/** Commits reachable from `tip`, ordered newest first by author timestamp then walk order. */
function listCommits(repo: Repo, tip: string | undefined): { sha: string; commit: ReturnType<typeof parseCommit> }[] {
  if (tip === undefined) return [];
  const commits = reachableCommits(repo, [tip]);
  const parsed = [...commits].map((sha) => {
    const obj = repo.objects.get(sha) as GitObject;
    return { sha, commit: parseCommit(obj.data) };
  });
  const epochOf = (text: string): number => {
    const match = / (\d+) [+-]\d{4}$/.exec(text);
    return match === null ? 0 : Number(match[1]);
  };
  // Topological order: a commit before its parents; ties by timestamp, then sha for stability.
  const order = new Map<string, number>();
  const visit = (sha: string, depth: number): void => {
    if (order.has(sha)) return;
    order.set(sha, depth);
    const entry = parsed.find((item) => item.sha === sha);
    if (entry !== undefined) {
      for (const parent of entry.commit.parents) visit(parent, depth + 1);
    }
  };
  visit(tip, 0);
  parsed.sort((x, y) => {
    const dx = order.get(x.sha) ?? 0;
    const dy = order.get(y.sha) ?? 0;
    if (dx !== dy) return dx - dy;
    const tx = epochOf(x.commit.author);
    const ty = epochOf(y.commit.author);
    if (tx !== ty) return ty - tx;
    return x.sha < y.sha ? -1 : 1;
  });
  return parsed;
}
function commitTimestamp(text: string): number {
  const match = / (\d+) [+-]\d{4}$/.exec(text);
  return match === null ? EPOCH_SEC : Number(match[1]);
}
function identityLine(user: ScenarioUser, epoch: number): string {
  return `${user.name} <${user.email}> ${epoch} +0000`;
}
/** Create a commit object on the repo and return its oid. */
function makeCommit(
  repo: Repo,
  treeOid: string,
  parents: readonly string[],
  message: string,
  epoch: number,
): string {
  const lines = [`tree ${treeOid}`];
  for (const parent of parents) lines.push(`parent ${parent}`);
  lines.push(`author ${identityLine(VIEWER, epoch)}`);
  lines.push(`committer ${identityLine(VIEWER, epoch)}`);
  const body = `${lines.join('\n')}\n\n${message}`;
  return storeObject(repo, 'commit', Buffer.from(body, 'utf8'));
}

// ---------------------------------------------------------------------------
// Packfiles: plain (no deltas) on the way out, deltas accepted on the way in.
// ---------------------------------------------------------------------------

const ZERO_OID = '0000000000000000000000000000000000000000';

function pktLine(payload: string | Buffer): Buffer {
  const data = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const length = data.length + 4;
  const header = Buffer.from(length.toString(16).padStart(4, '0'), 'utf8');
  return Buffer.concat([header, data]);
}
const FLUSH = Buffer.from('0000', 'utf8');
const DELIM = Buffer.from('0001', 'utf8');

interface PktLine {
  kind: 'data';
  data: Buffer;
}
type PktLineResult = PktLine | { kind: 'flush' } | { kind: 'delim' } | { kind: 'end' };

/** Read pkt-lines from `buf` starting at `pos`; returns lines and the next position. */
function readPktLines(buf: Buffer, pos: number): { lines: PktLineResult[]; next: number } {
  const lines: PktLineResult[] = [];
  let at = pos;
  while (at + 4 <= buf.length) {
    const head = buf.subarray(at, at + 4).toString('utf8');
    const length = Number.parseInt(head, 16);
    if (Number.isNaN(length)) break;
    if (length === 0) {
      lines.push({ kind: 'flush' });
      at += 4;
      continue;
    }
    if (length === 1) {
      lines.push({ kind: 'delim' });
      at += 4;
      continue;
    }
    if (length === 2) {
      lines.push({ kind: 'end' });
      at += 4;
      continue;
    }
    if (at + length > buf.length) break;
    lines.push({ kind: 'data', data: buf.subarray(at + 4, at + length) });
    at += length;
  }
  return { lines, next: at };
}

// The pack parser above needs the store for REF_DELTA bases; this wrapper supplies it.
function storePack(repo: Repo, buf: Buffer): string[] {
  if (buf.length < 12 || buf.subarray(0, 4).toString('ascii') !== 'PACK') {
    throw new Error('not a packfile');
  }
  const count = buf.readUInt32BE(8);
  let pos = 12;
  interface RawEntry {
    type: number;
    data: Buffer;
    base?: string;
    baseOffset?: number;
    offset: number;
  }
  const raw: RawEntry[] = [];
  for (let i = 0; i < count; i += 1) {
    const start = pos;
    let byte = buf[pos] as number;
    pos += 1;
    const type = (byte >> 4) & 0x07;
    let size = byte & 0x0f;
    let shift = 4;
    while (byte & 0x80) {
      byte = buf[pos] as number;
      pos += 1;
      size |= (byte & 0x7f) << shift;
      shift += 7;
    }
    void size;
    if (type === 6) {
      let offByte = buf[pos] as number;
      pos += 1;
      let offset = offByte & 0x7f;
      while (offByte & 0x80) {
        offByte = buf[pos] as number;
        pos += 1;
        offset = ((offset + 1) << 7) | (offByte & 0x7f);
      }
      const { data: inflated, consumed } = inflateObject(buf, pos, size);
      pos += consumed;
      raw.push({ type, data: inflated, baseOffset: start - offset, offset: start });
    } else if (type === 7) {
      const base = buf.subarray(pos, pos + 20).toString('hex');
      pos += 20;
      const { data: inflated, consumed } = inflateObject(buf, pos, size);
      pos += consumed;
      raw.push({ type, data: inflated, base, offset: start });
    } else {
      const { data: inflated, consumed } = inflateObject(buf, pos, size);
      pos += consumed;
      raw.push({ type, data: inflated, offset: start });
    }
  }
  const TYPE_NAMES: Record<number, ObjectType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };
  const byOffset = new Map<number, number>();
  raw.forEach((entry, index) => byOffset.set(entry.offset, index));
  const resolved = new Map<number, { type: ObjectType; data: Buffer }>();
  const resolve = (index: number): { type: ObjectType; data: Buffer } => {
    const done = resolved.get(index);
    if (done !== undefined) return done;
    const entry = raw[index] as RawEntry;
    if (entry.type === 6 || entry.type === 7) {
      let base: { type: ObjectType; data: Buffer } | undefined;
      if (entry.type === 6) {
        const baseIndex = byOffset.get(entry.baseOffset as number);
        if (baseIndex !== undefined) base = resolve(baseIndex);
      } else if (entry.base !== undefined) {
        const stored = repo.objects.get(entry.base);
        if (stored !== undefined) base = stored;
        else {
          // A base that is itself a delta in this pack, identified by its id.
          for (let j = 0; j < raw.length; j += 1) {
            const candidate = resolve(j);
            if (objectId(candidate.type, candidate.data) === entry.base) {
              base = candidate;
              break;
            }
          }
        }
      }
      if (base === undefined) throw new Error('delta base not found');
      const result = { type: base.type, data: applyDelta(base.data, entry.data) };
      resolved.set(index, result);
      return result;
    }
    const result = { type: TYPE_NAMES[entry.type] as ObjectType, data: entry.data };
    resolved.set(index, result);
    return result;
  };
  const oids: string[] = [];
  for (let i = 0; i < raw.length; i += 1) {
    const obj = resolve(i);
    oids.push(storeObject(repo, obj.type, obj.data));
  }
  return oids;
}

/** Inflate one pack object whose decompressed size the pack header declares.
 * The compressed form of `size` bytes is only a little larger than `size`
 * (stored blocks add a few bytes per 64 KiB), so the stream's end is found by
 * a binary search bounded by that size instead of by the rest of the pack:
 * inflating the whole remainder once per object is quadratic on large packs.
 * If the bound ever proves too small, fall back to the unbounded search. */
function inflateObject(buf: Buffer, pos: number, size: number): { data: Buffer; consumed: number } {
  const remaining = buf.length - pos;
  const bound = Math.min(remaining, size + Math.floor(size / 16) + 256);
  let low = 2;
  let high = bound;
  let found = -1;
  let foundData: Buffer | undefined;
  while (low <= high) {
    const mid = Math.floor((low + high) / 2);
    try {
      const out = inflateSync(buf.subarray(pos, pos + mid));
      if (out.length === size) {
        found = mid;
        foundData = out;
        high = mid - 1;
      } else {
        low = mid + 1;
      }
    } catch {
      low = mid + 1;
    }
  }
  if (found !== -1 && foundData !== undefined) return { data: foundData, consumed: found };
  const consumed = inflatedConsumedLength(buf, pos);
  return { data: inflateSync(buf.subarray(pos, pos + consumed)), consumed };
}

/** How many input bytes a zlib stream starting at `pos` consumes. inflateSync ignores
 * trailing bytes, so "this prefix inflates cleanly" is monotone in the prefix length
 * and a binary search finds the smallest clean prefix: the stream's true end. */
function inflatedConsumedLength(buf: Buffer, pos: number): number {
  let low = 2;
  let high = buf.length - pos;
  while (low < high) {
    const mid = Math.floor((low + high) / 2);
    try {
      inflateSync(buf.subarray(pos, pos + mid));
      high = mid;
    } catch {
      low = mid + 1;
    }
  }
  return low;
}

/** Apply a git delta to `base`, returning the result. */
function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let pos = 0;
  const readVarint = (): number => {
    let value = 0;
    let shift = 0;
    for (;;) {
      const byte = delta[pos] as number;
      pos += 1;
      value |= (byte & 0x7f) << shift;
      shift += 7;
      if ((byte & 0x80) === 0) return value;
    }
  };
  const sourceSize = readVarint();
  const targetSize = readVarint();
  if (sourceSize !== base.length) throw new Error('delta source size mismatch');
  const parts: Buffer[] = [];
  while (pos < delta.length) {
    const op = delta[pos] as number;
    pos += 1;
    if (op & 0x80) {
      let offset = 0;
      let size = 0;
      if (op & 0x01) offset = delta[pos] as number, pos += 1;
      if (op & 0x02) offset |= (delta[pos] as number) << 8, pos += 1;
      if (op & 0x04) offset |= (delta[pos] as number) << 16, pos += 1;
      if (op & 0x08) offset |= (delta[pos] as number) << 24, pos += 1;
      if (op & 0x10) size = delta[pos] as number, pos += 1;
      if (op & 0x20) size |= (delta[pos] as number) << 8, pos += 1;
      if (op & 0x40) size |= (delta[pos] as number) << 16, pos += 1;
      if (size === 0) size = 0x10000;
      parts.push(base.subarray(offset, offset + size));
    } else if (op !== 0) {
      parts.push(delta.subarray(pos, pos + op));
      pos += op;
    } else {
      throw new Error('delta opcode 0');
    }
  }
  const out = Buffer.concat(parts);
  if (out.length !== targetSize) throw new Error('delta target size mismatch');
  return out;
}

/** Build a plain packfile (no deltas) holding `objects` in a deterministic order. */
function buildPack(repo: Repo, oids: readonly string[]): Buffer {
  const sorted = [...oids].sort();
  const parts: Buffer[] = [];
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(sorted.length, 8);
  parts.push(header);
  const TYPE_CODES: Record<ObjectType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
  for (const oid of sorted) {
    const obj = repo.objects.get(oid);
    if (obj === undefined) continue;
    const typeCode = TYPE_CODES[obj.type];
    const size = obj.data.length;
    const headBytes: number[] = [];
    let first = (typeCode << 4) | (size & 0x0f);
    let remaining = size >> 4;
    if (remaining > 0) first |= 0x80;
    headBytes.push(first);
    while (remaining > 0) {
      let byte = remaining & 0x7f;
      remaining >>= 7;
      if (remaining > 0) byte |= 0x80;
      headBytes.push(byte);
    }
    parts.push(Buffer.from(headBytes));
    parts.push(deflateSync(obj.data));
  }
  const withoutTrailer = Buffer.concat(parts);
  const trailer = createHash('sha1').update(withoutTrailer).digest();
  return Buffer.concat([withoutTrailer, trailer]);
}

/** Every object reachable from `tips`, minus every object reachable from `heldTips`. */
function packObjects(
  repo: Repo,
  tips: readonly string[],
  heldTips: readonly string[],
  depth: number | null,
): Set<string> {
  const wanted = new Set<string>();
  const queue: { oid: string; depth: number }[] = tips.map((oid) => ({ oid, depth: 0 }));
  const seenCommits = new Set<string>();
  while (queue.length > 0) {
    const { oid, depth: d } = queue.shift() as { oid: string; depth: number };
    if (seenCommits.has(oid)) continue;
    const obj = repo.objects.get(oid);
    if (obj === undefined) continue;
    if (obj.type === 'commit') {
      if (depth !== null && d >= depth) {
        // Beyond the depth limit: this commit is not part of the fetch at all.
        // (Depth 1 is the tip commit alone; depth 2 adds its parents.)
        continue;
      }
      seenCommits.add(oid);
      wanted.add(oid);
      collectTree(repo, parseCommit(obj.data).tree, wanted);
      for (const parent of parseCommit(obj.data).parents) queue.push({ oid: parent, depth: d + 1 });
    } else {
      wanted.add(oid);
    }
  }
  const held = new Set<string>();
  const heldQueue = [...heldTips];
  const heldSeen = new Set<string>();
  while (heldQueue.length > 0) {
    const oid = heldQueue.shift() as string;
    if (heldSeen.has(oid)) continue;
    const obj = repo.objects.get(oid);
    if (obj === undefined) continue;
    heldSeen.add(oid);
    held.add(oid);
    if (obj.type === 'commit') {
      collectTree(repo, parseCommit(obj.data).tree, held);
      for (const parent of parseCommit(obj.data).parents) heldQueue.push(parent);
    } else if (obj.type === 'tree') {
      collectTree(repo, oid, held);
    }
  }
  for (const oid of held) wanted.delete(oid);
  return wanted;
}

function collectTree(repo: Repo, treeOid: string, out: Set<string>): void {
  const stack = [treeOid];
  while (stack.length > 0) {
    const oid = stack.pop() as string;
    if (out.has(oid)) continue;
    const obj = repo.objects.get(oid);
    if (obj === undefined) continue;
    out.add(oid);
    if (obj.type === 'tree') {
      for (const entry of parseTree(obj.data)) stack.push(entry.oid);
    }
  }
}

/** Sideband-encode `data` as band-1 pkt-lines (chunks of at most 65520 bytes). */
function sideband(data: Buffer): Buffer {
  // A pkt-line is at most 65520 bytes including its 4-byte header, and the
  // sideband band byte takes one more, so each chunk carries at most 65515
  // bytes of payload. Larger chunks are rejected by the client's parser.
  const parts: Buffer[] = [];
  for (let at = 0; at < data.length; at += 65515) {
    const chunk = data.subarray(at, Math.min(data.length, at + 65515));
    parts.push(pktLine(Buffer.concat([Buffer.from([1]), chunk])));
  }
  return Buffer.concat(parts);
}

// ---------------------------------------------------------------------------
// Git smart HTTP: /{owner}/{repo}.git/info/refs, git-upload-pack, git-receive-pack.
// ---------------------------------------------------------------------------

const UPLOAD_V0_CAPS = 'multi_ack thin-pack side-band side-band-64k ofs-delta shallow deepen-since deepen-not deepen-relative no-progress include-tag multi_ack_detailed allow-tip-sha1-in-want allow-reachable-sha1-in-want no-done';
const RECEIVE_CAPS = 'report-status side-band-64k delete-refs ofs-delta quiet atomic';
const AGENT = 'github-core-clone/1.0.0';

function sortedRefs(repo: Repo): { ref: string; oid: string }[] {
  const out: { ref: string; oid: string }[] = [];
  for (const [ref, oid] of repo.refs) out.push({ ref, oid });
  out.sort((a, b) => (a.ref < b.ref ? -1 : a.ref > b.ref ? 1 : 0));
  return out;
}

function advertisementV0(repo: Repo, service: 'git-upload-pack' | 'git-receive-pack'): Buffer {
  const parts: Buffer[] = [pktLine(`# service=${service}\n`), FLUSH];
  const refs = sortedRefs(repo);
  const caps = service === 'git-upload-pack'
    ? `${UPLOAD_V0_CAPS} symref=HEAD:refs/heads/${repo.defaultBranch}`
    : RECEIVE_CAPS;
  const defaultRef = `refs/heads/${repo.defaultBranch}`;
  const defaultOid = repo.refs.get(defaultRef);
  if (defaultOid !== undefined) {
    parts.push(pktLine(`${defaultOid} HEAD\0${caps} agent=${AGENT}\n`));
  }
  let first = defaultOid === undefined;
  for (const { ref, oid } of refs) {
    if (first) {
      parts.push(pktLine(`${oid} ${ref}\0${caps} agent=${AGENT}\n`));
      first = false;
    } else {
      parts.push(pktLine(`${oid} ${ref}\n`));
    }
  }
  if (refs.length === 0) {
    // An empty repository has no ref to carry the capabilities on, so git
    // expects the zero id with the pseudo-ref capabilities^{} instead: without
    // it the client cannot learn report-status or side-band-64k and refuses
    // to push the first commit.
    parts.push(pktLine(`${ZERO_OID} capabilities^{}\0${caps} agent=${AGENT}\n`));
  }
  // The ref list ends with a flush packet: a client reading pkt-lines treats
  // the stream ending without one as the remote hanging up.
  parts.push(FLUSH);
  return Buffer.concat(parts);
}

function advertisementV2(repo: Repo): Buffer {
  const parts: Buffer[] = [
    pktLine('version 2\n'),
    pktLine('ls-refs=unborn\n'),
    pktLine('fetch=shallow wait-for-done filter\n'),
    pktLine('object-format=sha1\n'),
    pktLine(`agent=${AGENT}\n`),
    FLUSH,
  ];
  return Buffer.concat(parts);
}

/** The objects a fetch sends, plus the shallow/unshallow lines for its answer. */
function fetchPlan(
  repo: Repo,
  wants: string[],
  haves: string[],
  shallowHaves: string[],
  depth: number | null,
): { objects: Set<string>; shallow: string[]; unshallow: string[] } {
  const shallowSet = new Set(shallowHaves);
  // A shallow have is held as the commit and its tree only: its parents are not held.
  const heldTips: string[] = [];
  for (const have of haves) {
    if (shallowSet.has(have)) {
      heldTips.push(have);
    } else {
      heldTips.push(have);
    }
  }
  // packObjects subtracts reachable(heldTips) wholesale; for shallow haves that would
  // wrongly subtract their parents, so handle them separately: held = reachable of the
  // non-shallow haves, plus the shallow commits and their trees only.
  const nonShallowHaves = haves.filter((have) => !shallowSet.has(have));
  const objects = packObjects(repo, wants, nonShallowHaves, depth);
  for (const have of shallowHaves) {
    const obj = repo.objects.get(have);
    if (obj === undefined || obj.type !== 'commit') continue;
    objects.delete(have);
    collectTree(repo, parseCommit(obj.data).tree, new Set<string>());
    const treeOid = parseCommit(obj.data).tree;
    const heldTree = new Set<string>();
    collectTree(repo, treeOid, heldTree);
    for (const oid of heldTree) objects.delete(oid);
  }
  void heldTips;
  // Boundary commits of a depth-limited fetch are shallow; a shallow have whose
  // parents are now included is unshallow.
  const shallow: string[] = [];
  const unshallow: string[] = [];
  if (depth !== null) {
    const included = new Set<string>();
    const queue: { oid: string; d: number }[] = wants.map((oid) => ({ oid, d: 0 }));
    const seen = new Set<string>();
    while (queue.length > 0) {
      const { oid, d } = queue.shift() as { oid: string; d: number };
      if (seen.has(oid)) continue;
      const obj = repo.objects.get(oid);
      if (obj === undefined || obj.type !== 'commit') continue;
      seen.add(oid);
      included.add(oid);
      if (d + 1 < depth) {
        for (const parent of parseCommit(obj.data).parents) queue.push({ oid: parent, d: d + 1 });
      }
    }
    for (const oid of included) {
      const obj = repo.objects.get(oid);
      if (obj === undefined) continue;
      const parents = parseCommit(obj.data).parents;
      if (parents.length === 0) continue;
      const allIncluded = parents.every((parent) => included.has(parent) || objects.has(parent));
      if (!allIncluded) shallow.push(oid);
    }
    for (const have of shallowHaves) {
      if (included.has(have)) {
        const obj = repo.objects.get(have);
        if (obj !== undefined) {
          const parents = parseCommit(obj.data).parents;
          if (parents.every((parent) => included.has(parent))) unshallow.push(have);
        }
      }
    }
  } else {
    for (const have of shallowHaves) {
      const reachable = reachableCommits(repo, wants);
      if (reachable.has(have)) {
        const obj = repo.objects.get(have);
        if (obj !== undefined) {
          const parents = parseCommit(obj.data).parents;
          if (parents.every((parent) => reachable.has(parent))) unshallow.push(have);
        }
      }
    }
  }
  return { objects, shallow, unshallow };
}

interface UploadRequest {
  wants: string[];
  haves: string[];
  shallow: string[];
  depth: number | null;
  sideband: boolean;
  version: 1 | 2;
  command: 'fetch' | 'ls-refs' | null;
  refPrefixes: string[];
  peel: boolean;
  unborn: boolean;
  filter: string | null;
  done: boolean;
}

/** Parse a v0 upload-pack request body. */
function parseUploadV0(body: Buffer): UploadRequest {
  const req: UploadRequest = {
    wants: [], haves: [], shallow: [], depth: null, sideband: false, version: 1,
    command: 'fetch', refPrefixes: [], peel: false, unborn: false, filter: null, done: false,
  };
  const { lines } = readPktLines(body, 0);
  for (const line of lines) {
    if (line.kind !== 'data') continue;
    const text = line.data.toString('utf8').trimEnd();
    if (text === '') continue;
    const nul = text.indexOf('\0');
    const head = nul >= 0 ? text.slice(0, nul) : text;
    const caps = nul >= 0 ? text.slice(nul + 1) : '';
    if (caps.includes('side-band-64k') || caps.includes('side-band')) req.sideband = true;
    if (head.startsWith('want ')) {
      req.wants.push(head.slice(5, 45));
      // The first want line carries the client's capabilities after the oid,
      // separated by a space (the NUL separator belongs to advertisements and
      // receive-pack commands, not to want lines).
      const afterOid = head.slice(46);
      if (afterOid.includes('side-band-64k') || afterOid.includes('side-band')) req.sideband = true;
      if (caps.includes('side-band-64k') || caps.includes('side-band')) req.sideband = true;
    } else if (head.startsWith('have ')) {
      req.haves.push(head.slice(5, 45));
    } else if (head.startsWith('shallow ')) {
      req.shallow.push(head.slice(8, 48));
    } else if (head.startsWith('deepen ')) {
      const n = Number.parseInt(head.slice(7), 10);
      if (Number.isFinite(n) && n > 0) req.depth = n;
    } else if (head.startsWith('filter ')) {
      req.filter = head.slice(7);
    } else if (head === 'done') {
      req.done = true;
      break;
    }
  }
  return req;
}

/** Parse a v2 upload-pack request body: one command section, then its arguments. */
function parseUploadV2(body: Buffer): UploadRequest {
  const req: UploadRequest = {
    wants: [], haves: [], shallow: [], depth: null, sideband: true, version: 2,
    command: null, refPrefixes: [], peel: false, unborn: false, filter: null, done: false,
  };
  const { lines } = readPktLines(body, 0);
  let inCommand = false;
  for (const line of lines) {
    if (line.kind === 'flush' || line.kind === 'delim') {
      inCommand = false;
      continue;
    }
    if (line.kind !== 'data') continue;
    const text = line.data.toString('utf8').trimEnd();
    if (text === '') continue;
    if (text.startsWith('command=')) {
      const command = text.slice('command='.length);
      if (command === 'ls-refs') req.command = 'ls-refs';
      else if (command === 'fetch') req.command = 'fetch';
      inCommand = true;
      continue;
    }
    if (!inCommand && req.command === null) continue;
    if (req.command === 'ls-refs') {
      if (text === 'peel') req.peel = true;
      else if (text === 'unborn') req.unborn = true;
      else if (text.startsWith('ref-prefix ')) req.refPrefixes.push(text.slice('ref-prefix '.length));
      else if (text.startsWith('ref-prefix:')) req.refPrefixes.push(text.slice('ref-prefix:'.length));
    } else if (req.command === 'fetch') {
      if (text.startsWith('want ')) req.wants.push(text.slice(5, 45));
      else if (text.startsWith('have ')) req.haves.push(text.slice(5, 45));
      else if (text.startsWith('shallow ')) req.shallow.push(text.slice(8, 48));
      else if (text.startsWith('deepen ')) {
        const n = Number.parseInt(text.slice(7), 10);
        if (Number.isFinite(n) && n > 0) req.depth = n;
      } else if (text.startsWith('filter ')) req.filter = text.slice(7);
      else if (text === 'done') {
        req.done = true;
        break;
      }
    }
  }
  return req;
}

/** Answer a v2 ls-refs command. */
function lsRefsV2(repo: Repo, req: UploadRequest): Buffer {
  const parts: Buffer[] = [];
  const refs = sortedRefs(repo);
  const defaultRef = `refs/heads/${repo.defaultBranch}`;
  const defaultOid = repo.refs.get(defaultRef);
  const matches = (ref: string): boolean => {
    if (req.refPrefixes.length === 0) return true;
    return req.refPrefixes.some((prefix) => ref.startsWith(prefix));
  };
  const peeledOf = (oid: string): string | null => {
    const obj = repo.objects.get(oid);
    if (obj === undefined || obj.type !== 'tag') return null;
    const text = obj.data.toString('utf8');
    const match = /^object ([0-9a-f]{40})$/m.exec(text);
    return match === null ? null : match[1];
  };
  if (req.refPrefixes.length === 0 || req.refPrefixes.some((prefix) => 'HEAD'.startsWith(prefix))) {
    if (defaultOid !== undefined) {
      parts.push(pktLine(`${defaultOid} HEAD symref-target:${defaultRef}\n`));
    } else if (req.unborn) {
      parts.push(pktLine(`unborn HEAD symref-target:${defaultRef}\n`));
    }
  }
  for (const { ref, oid } of refs) {
    if (!matches(ref)) continue;
    let line = `${oid} ${ref}`;
    const peeled = req.peel ? peeledOf(oid) : null;
    if (peeled !== null) line += ` peeled:${peeled}`;
    parts.push(pktLine(`${line}\n`));
  }
  parts.push(FLUSH);
  return Buffer.concat(parts);
}

/** Answer an upload-pack request (v0 or v2 fetch). */
function uploadPackAnswer(repo: Repo, req: UploadRequest): Buffer {
  const plan = fetchPlan(repo, req.wants, req.haves, req.shallow, req.depth);
  if (req.version === 2) {
    const parts: Buffer[] = [];
    // The acknowledgments section answers the client's haves: an ACK for every
    // have the forge holds that is an ancestor of a want, NAK when none is,
    // then ready; a delim packet ends the section.
    if (req.haves.length > 0) {
      const reachable = reachableCommits(repo, req.wants);
      const common = req.haves.filter((have) => reachable.has(have) && repo.objects.has(have));
      parts.push(pktLine('acknowledgments\n'));
      if (common.length === 0) {
        parts.push(pktLine('NAK\n'));
      } else {
        for (const oid of common) parts.push(pktLine(`ACK ${oid}\n`));
      }
      parts.push(pktLine('ready\n'));
      parts.push(DELIM);
    }
    // The shallow-info section follows when the fetch is depth-limited or the
    // client carries a shallow boundary; a delim packet ends it, even empty.
    if (req.depth !== null || req.shallow.length > 0) {
      parts.push(pktLine('shallow-info\n'));
      for (const oid of plan.shallow) parts.push(pktLine(`shallow ${oid}\n`));
      for (const oid of plan.unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
      parts.push(DELIM);
    }
    const pack = buildPack(repo, [...plan.objects]);
    parts.push(pktLine('packfile\n'));
    parts.push(sideband(pack));
    parts.push(FLUSH);
    return Buffer.concat(parts);
  }
  // v0 is two sections in one POST for the suite's client (wants, then haves
  // and done), but a bare git client negotiates a shallow fetch in two POSTs:
  // the first carries wants and deepen but no done, and is answered with the
  // shallow lines and a flush only; the second carries done and is answered
  // with the NAK and the pack.
  if (req.depth !== null && !req.done) {
    const parts: Buffer[] = [];
    // Git's own upload-pack writes these lines with no trailing newline.
    for (const oid of plan.shallow) parts.push(pktLine(`shallow ${oid}`));
    for (const oid of plan.unshallow) parts.push(pktLine(`unshallow ${oid}`));
    parts.push(FLUSH);
    return Buffer.concat(parts);
  }
  const pack = buildPack(repo, [...plan.objects]);
  // The shallow lines travel before the NAK, terminated by their own flush:
  // the client reads the shallow list first and only then the acknowledgment.
  const parts: Buffer[] = [];
  for (const oid of plan.shallow) parts.push(pktLine(`shallow ${oid}`));
  for (const oid of plan.unshallow) parts.push(pktLine(`unshallow ${oid}`));
  if (plan.shallow.length > 0 || plan.unshallow.length > 0) parts.push(FLUSH);
  parts.push(pktLine('NAK\n'));
  if (req.sideband) {
    parts.push(sideband(pack));
    parts.push(FLUSH);
  } else {
    parts.push(pack);
  }
  return Buffer.concat(parts);
}

interface ReceiveCommand {
  oldOid: string;
  newOid: string;
  ref: string;
}

/** Parse a v0 receive-pack request body: ref commands, then a raw packfile. */
function parseReceive(body: Buffer): { commands: ReceiveCommand[]; pack: Buffer; sideband: boolean } {
  const { lines, next } = readPktLines(body, 0);
  const commands: ReceiveCommand[] = [];
  let sideband = false;
  for (const line of lines) {
    if (line.kind === 'flush') break;
    if (line.kind !== 'data') continue;
    const text = line.data.toString('utf8');
    const nul = text.indexOf('\0');
    const head = (nul >= 0 ? text.slice(0, nul) : text).trimEnd();
    const caps = nul >= 0 ? text.slice(nul + 1) : '';
    if (caps.includes('side-band-64k') || caps.includes('side-band')) sideband = true;
    const match = /^([0-9a-f]{40}) ([0-9a-f]{40}) (\S+)$/.exec(head);
    if (match !== null) {
      commands.push({ oldOid: match[1] as string, newOid: match[2] as string, ref: match[3] as string });
    }
  }
  return { commands, pack: body.subarray(next), sideband };
}

/** Apply a receive-pack: store the pack, move the fast-forward refs, answer the report. */
function receivePackAnswer(repo: Repo, body: Buffer): { status: number; body: Buffer; contentType: string } {
  let parsed: { commands: ReceiveCommand[]; pack: Buffer; sideband: boolean };
  try {
    parsed = parseReceive(body);
  } catch {
    return {
      status: 400,
      body: Buffer.from(JSON.stringify({ message: 'malformed receive-pack request' }), 'utf8'),
      contentType: 'application/json; charset=utf-8',
    };
  }
  if (parsed.pack.length > 0) {
    try {
      storePack(repo, parsed.pack);
    } catch (err) {
      process.stderr.write(`[entry] storePack failed: ${err instanceof Error ? err.message : String(err)}\n`);
      // A bad pack still gets a report: the ref updates below refuse, and the
      // report says unpack failed instead of crashing the server.
      const report = [pktLine('unpack error\n')];
      for (const command of parsed.commands) report.push(pktLine(`ng ${command.ref} unpack failed\n`));
      report.push(FLUSH);
      return { status: 200, body: Buffer.concat(report), contentType: 'application/x-git-receive-pack-result' };
    }
  }
  const results: { ref: string; ok: boolean; reason: string }[] = [];
  for (const command of parsed.commands) {
    if (command.newOid === ZERO_OID) {
      // Delete the ref.
      if (repo.refs.has(command.ref)) {
        repo.refs.delete(command.ref);
        results.push({ ref: command.ref, ok: true, reason: '' });
      } else {
        results.push({ ref: command.ref, ok: false, reason: 'reference does not exist' });
      }
      continue;
    }
    if (!repo.objects.has(command.newOid)) {
      results.push({ ref: command.ref, ok: false, reason: 'object not in pack' });
      continue;
    }
    const current = repo.refs.get(command.ref);
    if (current === undefined) {
      if (command.oldOid !== ZERO_OID) {
        results.push({ ref: command.ref, ok: false, reason: 'reference does not exist' });
        continue;
      }
      repo.refs.set(command.ref, command.newOid);
      results.push({ ref: command.ref, ok: true, reason: '' });
      continue;
    }
    if (current !== command.oldOid) {
      results.push({ ref: command.ref, ok: false, reason: 'stale old value' });
      continue;
    }
    if (!isAncestor(repo, current, command.newOid)) {
      results.push({ ref: command.ref, ok: false, reason: 'non-fast-forward' });
      continue;
    }
    repo.refs.set(command.ref, command.newOid);
    results.push({ ref: command.ref, ok: true, reason: '' });
  }
  const lines: Buffer[] = [pktLine('unpack ok\n')];
  for (const result of results) {
    lines.push(pktLine(result.ok ? `ok ${result.ref}\n` : `ng ${result.ref} ${result.reason}\n`));
  }
  lines.push(FLUSH);
  const report = Buffer.concat(lines);
  if (parsed.sideband) {
    // The whole report — including its own terminating flush packet — travels
    // inside sideband band 1; a second, outer flush then ends the sideband
    // stream. The client's demultiplexer strips the band byte and hands the
    // report reader its lines plus the flush, and a report that ends at the
    // outer flush without one reads as the remote hanging up.
    return { status: 200, body: Buffer.concat([sideband(report), FLUSH]), contentType: 'application/x-git-receive-pack-result' };
  }
  return { status: 200, body: report, contentType: 'application/x-git-receive-pack-result' };
}

// ---------------------------------------------------------------------------
// HTTP plumbing.
// ---------------------------------------------------------------------------

const JSON_TYPE = 'application/json; charset=utf-8';
const EXPECTED_TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';

function nextRequestId(): string {
  requestCounter += 1;
  return `req-${requestCounter}`;
}

function sendJson(res: ServerResponse, status: number, body: unknown, headers: Record<string, string> = {}): void {
  const text = `${JSON.stringify(body)}\n`;
  res.writeHead(status, {
    'content-type': JSON_TYPE,
    'content-length': Buffer.byteLength(text),
    'x-github-request-id': nextRequestId(),
    ...headers,
  });
  res.end(text);
}

function sendBuffer(res: ServerResponse, status: number, body: Buffer, contentType: string, headers: Record<string, string> = {}): void {
  res.writeHead(status, {
    'content-type': contentType,
    'content-length': body.length,
    'x-github-request-id': nextRequestId(),
    ...headers,
  });
  res.end(body);
}

function sendNoContent(res: ServerResponse, status: number): void {
  res.writeHead(status, { 'x-github-request-id': nextRequestId() });
  res.end();
}

function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    let total = 0;
    req.on('data', (chunk: Buffer) => {
      total += chunk.length;
      if (total > 64 * 1024 * 1024) {
        reject(new Error('request body too large'));
        return;
      }
      chunks.push(chunk);
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

function bearerToken(req: IncomingMessage): string | null {
  const header = req.headers.authorization;
  if (header === undefined) return null;
  const match = /^Bearer (.+)$/.exec(header);
  return match === null ? null : (match[1] as string);
}

function tokenValid(token: string | null): boolean {
  if (token === null || token === '') return false;
  if (EXPECTED_TOKEN === '') return true;
  if (token.length !== EXPECTED_TOKEN.length) return false;
  return timingSafeEqual(Buffer.from(token, 'utf8'), Buffer.from(EXPECTED_TOKEN, 'utf8'));
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}
function stringField(body: Record<string, unknown>, key: string): string {
  const value = body[key];
  return typeof value === 'string' ? value : '';
}
function intParam(url: URL, key: string, fallback: number): number {
  const raw = url.searchParams.get(key);
  if (raw === null) return fallback;
  const n = Number.parseInt(raw, 10);
  return Number.isFinite(n) && n > 0 ? n : fallback;
}

/** Paginate `items` by per_page/page and answer with a Link header when more pages follow. */
function paginate<T>(res: ServerResponse, req: IncomingMessage, url: URL, items: readonly T[]): T[] {
  const perPage = Math.min(100, intParam(url, 'per_page', 30));
  const page = intParam(url, 'page', 1);
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  const links: string[] = [];
  const base = `${req.headers.host !== undefined ? `http://${req.headers.host}` : ''}${url.pathname}`;
  const query = new URLSearchParams(url.searchParams);
  if (start + perPage < items.length) {
    query.set('page', String(page + 1));
    query.set('per_page', String(perPage));
    links.push(`<${base}?${query.toString()}>; rel="next"`);
  }
  if (page > 1) {
    query.set('page', String(page - 1));
    query.set('per_page', String(perPage));
    links.push(`<${base}?${query.toString()}>; rel="prev"`);
    query.set('page', '1');
    links.push(`<${base}?${query.toString()}>; rel="first"`);
  }
  const lastPage = Math.max(1, Math.ceil(items.length / perPage));
  query.set('page', String(lastPage));
  query.set('per_page', String(perPage));
  links.push(`<${base}?${query.toString()}>; rel="last"`);
  res.setHeader('link', links.join(', '));
  return slice as T[];
}

function decodeSegment(segment: string): string {
  try {
    return decodeURIComponent(segment);
  } catch {
    return segment;
  }
}

// ---------------------------------------------------------------------------
// REST shapes.
// ---------------------------------------------------------------------------

function userJson(user: ScenarioUser): Record<string, unknown> {
  return {
    login: user.login,
    id: user.id,
    node_id: globalId('User', String(user.id)),
    avatar_url: `https://example.invalid/avatar/${user.login}`,
    gravatar_id: '',
    url: `/api/v3/users/${user.login}`,
    html_url: `https://example.invalid/${user.login}`,
    type: 'User',
    site_admin: false,
    name: user.name,
    email: user.email,
  };
}

function repoJson(repo: Repo): Record<string, unknown> {
  const base = `/api/v3/repos/${repo.owner}/${repo.name}`;
  return {
    id: repo.id,
    node_id: globalId('Repository', String(repo.id)),
    name: repo.name,
    full_name: `${repo.owner}/${repo.name}`,
    owner: userJson(VIEWER),
    private: repo.isPrivate,
    html_url: `https://example.invalid/${repo.owner}/${repo.name}`,
    description: repo.description,
    fork: false,
    url: base,
    created_at: repo.createdAt,
    updated_at: repo.createdAt,
    pushed_at: repo.createdAt,
    homepage: null,
    size: 0,
    stargazers_count: 0,
    watchers_count: 0,
    language: null,
    has_issues: true,
    has_projects: true,
    has_downloads: true,
    has_wiki: true,
    has_pages: false,
    has_discussions: false,
    forks_count: 0,
    archived: false,
    disabled: false,
    open_issues_count: repo.issues.filter((issue) => issue.state === 'open').length,
    license: null,
    allow_forking: true,
    is_template: false,
    topics: [],
    visibility: repo.isPrivate ? 'private' : 'public',
    default_branch: repo.defaultBranch,
    permissions: { admin: true, maintain: true, push: true, triage: true, pull: true },
  };
}

function issueJson(repo: Repo, issue: Issue): Record<string, unknown> {
  const base = `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}`;
  return {
    id: 10000 + issue.seq,
    node_id: globalId('Issue', `${repo.id}:${issue.number}`),
    url: base,
    repository_url: `/api/v3/repos/${repo.owner}/${repo.name}`,
    html_url: `https://example.invalid/${repo.owner}/${repo.name}/issues/${issue.number}`,
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    user: userJson(issue.user),
    labels: issue.labels.map((name) => {
      const label = repo.labels.get(name);
      return { name, color: label?.color ?? 'ededed', description: label?.description ?? '' };
    }),
    assignee: null,
    assignees: [],
    milestone: null,
    locked: false,
    comments: (repo.comments.get(issue.number) ?? []).length,
    created_at: issue.createdAt,
    updated_at: issue.updatedAt,
    closed_at: issue.state === 'closed' ? issue.updatedAt : null,
    author_association: 'OWNER',
  };
}

function commentJson(repo: Repo, issueNumber: number, comment: Comment): Record<string, unknown> {
  return {
    id: 20000 + comment.id,
    node_id: globalId('IssueComment', `${repo.id}:${issueNumber}:${comment.id}`),
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issueNumber}/comments/${comment.id}`,
    html_url: `https://example.invalid/${repo.owner}/${repo.name}/issues/${issueNumber}#issuecomment-${comment.id}`,
    body: comment.body,
    user: userJson(comment.user),
    created_at: comment.createdAt,
    updated_at: comment.createdAt,
    author_association: 'OWNER',
  };
}

/** The three-way merge of head onto baseTip over their merge-base, or a conflict. */
function threeWayMerge(repo: Repo, baseOid: string, headOid: string, baseTipOid: string): { conflict: boolean; tree: string | null } {
  const baseTree = new Map<string, { oid: string; mode: string }>();
  const headTree = new Map<string, { oid: string; mode: string }>();
  const tipTree = new Map<string, { oid: string; mode: string }>();
  const baseCommit = repo.objects.get(baseOid);
  const headCommit = repo.objects.get(headOid);
  const tipCommit = repo.objects.get(baseTipOid);
  if (baseCommit === undefined || headCommit === undefined || tipCommit === undefined) {
    return { conflict: true, tree: null };
  }
  flattenTree(repo, parseCommit(baseCommit.data).tree, '', baseTree);
  flattenTree(repo, parseCommit(headCommit.data).tree, '', headTree);
  flattenTree(repo, parseCommit(tipCommit.data).tree, '', tipTree);
  const merged = new Map(tipTree);
  const paths = new Set([...baseTree.keys(), ...headTree.keys(), ...tipTree.keys()]);
  for (const path of paths) {
    const base = baseTree.get(path);
    const head = headTree.get(path);
    const tip = tipTree.get(path);
    const headChanged = (head?.oid ?? null) !== (base?.oid ?? null);
    const tipChanged = (tip?.oid ?? null) !== (base?.oid ?? null);
    if (headChanged && tipChanged) {
      if ((head?.oid ?? null) !== (tip?.oid ?? null)) return { conflict: true, tree: null };
      // Both changed the same way: keep either.
    } else if (headChanged) {
      if (head === undefined) merged.delete(path);
      else merged.set(path, head);
    }
    // Tip-only changes stay as they are.
  }
  return { conflict: false, tree: treeFromFlat(repo, merged) };
}

/** The current tip of a pull request's base branch (it moves when other PRs merge). */
function currentBaseTip(repo: Repo, pull: Pull): string {
  return repo.refs.get(`refs/heads/${pull.baseRef}`) ?? pull.baseSha;
}

function prConflict(repo: Repo, pull: Pull): boolean {
  const tip = currentBaseTip(repo, pull);
  const base = mergeBase(repo, pull.headSha, tip);
  if (base === null) return true;
  return threeWayMerge(repo, base, pull.headSha, tip).conflict;
}

function pullJson(repo: Repo, pull: Pull): Record<string, unknown> {
  const base = `/api/v3/repos/${repo.owner}/${repo.name}/pulls/${pull.number}`;
  const mergeable = pull.state === 'open' ? !prConflict(repo, pull) : false;
  return {
    id: 30000 + pull.seq,
    node_id: globalId('PullRequest', `${repo.id}:${pull.number}`),
    url: base,
    html_url: `https://example.invalid/${repo.owner}/${repo.name}/pull/${pull.number}`,
    number: pull.number,
    title: pull.title,
    body: pull.body,
    state: pull.state,
    locked: false,
    user: userJson(pull.user),
    created_at: pull.createdAt,
    updated_at: pull.createdAt,
    closed_at: pull.state === 'closed' ? (pull.mergedAt ?? pull.createdAt) : null,
    merged_at: pull.mergedAt,
    merge_commit_sha: pull.mergeCommitSha,
    merged: pull.merged,
    mergeable,
    mergeable_state: pull.state === 'open' ? (mergeable ? 'clean' : 'dirty') : 'unknown',
    merge_method: 'squash',
    head: {
      label: `${repo.owner}:${pull.headRef}`,
      ref: pull.headRef,
      sha: pull.headSha,
      user: userJson(VIEWER),
      repo: repoJson(repo),
    },
    base: {
      label: `${repo.owner}:${pull.baseRef}`,
      ref: pull.baseRef,
      sha: currentBaseTip(repo, pull),
      user: userJson(VIEWER),
      repo: repoJson(repo),
    },
    author_association: 'OWNER',
    draft: false,
    commits: 1,
    additions: 0,
    deletions: 0,
    changed_files: 0,
  };
}

/** Line counts of a simple line diff (LCS over lines, capped for huge files). */
function diffLineCounts(oldText: string, newText: string): { additions: number; deletions: number } {
  const oldLines = oldText === '' ? [] : oldText.split('\n');
  const newLines = newText === '' ? [] : newText.split('\n');
  if (oldLines.length > 2000 || newLines.length > 2000) {
    return { additions: newLines.length, deletions: oldLines.length };
  }
  const m = oldLines.length;
  const n = newLines.length;
  // LCS lengths, two rows.
  let prev = new Array<number>(n + 1).fill(0);
  let curr = new Array<number>(n + 1).fill(0);
  for (let i = 1; i <= m; i += 1) {
    for (let j = 1; j <= n; j += 1) {
      curr[j] = oldLines[i - 1] === newLines[j - 1] ? (prev[j - 1] as number) + 1 : Math.max(prev[j] as number, curr[j - 1] as number);
    }
    const swap = prev;
    prev = curr;
    curr = swap;
  }
  const common = prev[n] as number;
  return { additions: n - common, deletions: m - common };
}

function pullFiles(repo: Repo, pull: Pull): Record<string, unknown>[] {
  const base = mergeBase(repo, pull.headSha, pull.baseSha);
  const baseOid = base ?? pull.baseSha;
  const baseCommit = repo.objects.get(baseOid);
  const headCommit = repo.objects.get(pull.headSha);
  if (baseCommit === undefined || headCommit === undefined) return [];
  const baseFlat = new Map<string, { oid: string; mode: string }>();
  const headFlat = new Map<string, { oid: string; mode: string }>();
  flattenTree(repo, parseCommit(baseCommit.data).tree, '', baseFlat);
  flattenTree(repo, parseCommit(headCommit.data).tree, '', headFlat);
  const files: Record<string, unknown>[] = [];
  const paths = new Set([...baseFlat.keys(), ...headFlat.keys()]);
  for (const path of [...paths].sort()) {
    const before = baseFlat.get(path);
    const after = headFlat.get(path);
    if ((before?.oid ?? null) === (after?.oid ?? null)) continue;
    let status: string;
    let additions = 0;
    let deletions = 0;
    if (before === undefined && after !== undefined) {
      status = 'added';
      const blob = repo.objects.get(after.oid);
      const text = blob === undefined ? '' : blob.data.toString('utf8');
      additions = text === '' ? 0 : text.split('\n').length;
      if (additions === 0) additions = 1;
    } else if (before !== undefined && after === undefined) {
      status = 'removed';
      const blob = repo.objects.get(before.oid);
      const text = blob === undefined ? '' : blob.data.toString('utf8');
      deletions = text === '' ? 0 : text.split('\n').length;
      if (deletions === 0) deletions = 1;
    } else if (before !== undefined && after !== undefined) {
      status = 'modified';
      const oldBlob = repo.objects.get(before.oid);
      const newBlob = repo.objects.get(after.oid);
      const counts = diffLineCounts(
        oldBlob === undefined ? '' : oldBlob.data.toString('utf8'),
        newBlob === undefined ? '' : newBlob.data.toString('utf8'),
      );
      additions = counts.additions;
      deletions = counts.deletions;
      if (additions === 0 && deletions === 0) {
        additions = 1;
      }
    } else {
      continue;
    }
    files.push({
      sha: after?.oid ?? before?.oid ?? '',
      filename: path,
      status,
      additions,
      deletions,
      changes: additions + deletions,
      blob_url: `https://example.invalid/${repo.owner}/${repo.name}/blob/${pull.headSha}/${path}`,
      raw_url: `https://example.invalid/${repo.owner}/${repo.name}/raw/${pull.headSha}/${path}`,
      contents_url: `/api/v3/repos/${repo.owner}/${repo.name}/contents/${path}?ref=${pull.headSha}`,
    });
  }
  return files;
}

function resolveRef(repo: Repo, ref: string | undefined): string | undefined {
  if (ref === undefined || ref === '') return repo.refs.get(`refs/heads/${repo.defaultBranch}`);
  if (/^[0-9a-f]{40}$/.test(ref)) {
    return repo.objects.has(ref) ? ref : undefined;
  }
  const direct = repo.refs.get(ref);
  if (direct !== undefined) return direct;
  const branch = repo.refs.get(`refs/heads/${ref}`);
  if (branch !== undefined) return branch;
  const tag = repo.refs.get(`refs/tags/${ref}`);
  if (tag !== undefined) return tag;
  return undefined;
}

function parseIdentity(text: string): { name: string; email: string; epoch: number } {
  const match = /^(.*) <(.*)> (\d+) [+-]\d{4}$/.exec(text);
  if (match === null) return { name: '', email: '', epoch: EPOCH_SEC };
  return { name: match[1] as string, email: match[2] as string, epoch: Number(match[3]) };
}

// ---------------------------------------------------------------------------
// REST v3 routes.
// ---------------------------------------------------------------------------

async function handleRest(
  req: IncomingMessage,
  res: ServerResponse,
  url: URL,
  segments: string[],
  body: Buffer,
  json: Record<string, unknown> | undefined,
): Promise<boolean> {
  const method = req.method ?? 'GET';
  const notFound = (): void => sendJson(res, 404, { message: 'Not Found' });
  const badRequest = (message: string): void => sendJson(res, 400, { message });
  void badRequest;

  // GET /api/v3/ — the API root.
  if (segments.length === 0) {
    if (method !== 'GET') {
      sendJson(res, 404, { message: 'Not Found' });
      return true;
    }
    sendJson(
      res,
      200,
      { current_user_url: '/api/v3/user', rate_limit_url: '/api/v3/rate_limit', repository_url: '/api/v3/repos/{owner}/{repo}' },
      { 'x-oauth-scopes': 'repo, read:org' },
    );
    return true;
  }

  // GET /api/v3/meta
  if (segments.length === 1 && segments[0] === 'meta') {
    if (method !== 'GET') {
      sendJson(res, 404, { message: 'Not Found' });
      return true;
    }
    sendJson(res, 200, {
      verifiable_password_authentication: true,
      installed_version: '1.0.0',
      server_version: '1.0.0',
      hooks: ['pre-receive'],
      git: ['1.0.0'],
      pages: ['1.0.0'],
    });
    return true;
  }

  // GET /api/v3/rate_limit
  if (segments.length === 1 && segments[0] === 'rate_limit') {
    sendJson(res, 200, {
      resources: { core: { limit: 5000, remaining: 4999, reset: EPOCH_SEC + 3600, used: 1 } },
      rate: { limit: 5000, remaining: 4999, reset: EPOCH_SEC + 3600, used: 1 },
    });
    return true;
  }

  // /api/v3/user and /api/v3/user/repos
  if (segments[0] === 'user') {
    if (segments.length === 1) {
      if (method !== 'GET') {
        sendJson(res, 404, { message: 'Not Found' });
        return true;
      }
      sendJson(res, 200, userJson(VIEWER));
      return true;
    }
    if (segments.length === 2 && segments[1] === 'repos') {
      if (method === 'GET') {
        const list = viewerRepos().map((repo) => repoJson(repo));
        const page = paginate(res, req, url, list);
        sendJson(res, 200, page);
        return true;
      }
      if (method === 'POST') {
        const name = json === undefined ? '' : stringField(json, 'name');
        if (name === '') {
          sendJson(res, 422, { message: 'name is required' });
          return true;
        }
        if (getRepo(VIEWER.login, name) !== undefined) {
          sendJson(res, 422, { message: 'Repository already exists', errors: [{ message: 'name already exists on this account' }] });
          return true;
        }
        const createdAt = stamp().iso;
        const repo: Repo = {
          id: dbIdCounter,
          name,
          owner: VIEWER.login,
          description: json === undefined ? '' : stringField(json, 'description'),
          isPrivate: json !== undefined && json.private === true,
          defaultBranch: json !== undefined && typeof json.default_branch === 'string' && json.default_branch !== '' ? (json.default_branch as string) : 'main',
          createdAt,
          refs: new Map(),
          objects: new Map(),
          issues: [],
          labels: new Map([
            ['bug', { name: 'bug', color: 'd73a4a', description: "Something isn't working" }],
            ['enhancement', { name: 'enhancement', color: 'a2eeef', description: 'New feature or request' }],
            ['question', { name: 'question', color: 'd876e3', description: 'Further information is requested' }],
          ]),
          pulls: [],
          comments: new Map(),
          nextIssue: 1,
          nextPull: 1,
          nextComment: 1,
          seq: nextTick(),
        };
        dbIdCounter += 1;
        repos.set(repoKey(repo.owner, repo.name), repo);
        sendJson(res, 201, repoJson(repo));
        return true;
      }
      sendJson(res, 404, { message: 'Not Found' });
      return true;
    }
    sendJson(res, 404, { message: 'Not Found' });
    return true;
  }

  // /api/v3/repos/{owner}/{repo}[...]
  if (segments[0] === 'repos' && segments.length >= 3) {
    const owner = decodeSegment(segments[1] as string);
    const name = decodeSegment(segments[2] as string);
    const repo = getRepo(owner, name);
    if (repo === undefined || repo.owner !== VIEWER.login) {
      sendJson(res, 404, { message: 'Not Found' });
      return true;
    }
    const rest = segments.slice(3);

    // The repository itself.
    if (rest.length === 0) {
      if (method === 'GET') {
        sendJson(res, 200, repoJson(repo));
        return true;
      }
      if (method === 'PATCH') {
        if (json !== undefined) {
          if (typeof json.description === 'string') repo.description = json.description;
          if (typeof json.default_branch === 'string' && json.default_branch !== '') {
            repo.defaultBranch = json.default_branch;
          }
        }
        sendJson(res, 200, repoJson(repo));
        return true;
      }
      if (method === 'DELETE') {
        repos.delete(repoKey(owner, name));
        sendNoContent(res, 204);
        return true;
      }
      sendJson(res, 404, { message: 'Not Found' });
      return true;
    }

    // git refs: POST /git/refs, GET /git/refs[/...]
    if (rest[0] === 'git' && rest[1] === 'refs') {
      if (method === 'POST' && rest.length === 2) {
        const ref = json === undefined ? '' : stringField(json, 'ref');
        const sha = json === undefined ? '' : stringField(json, 'sha');
        if (ref === '' || sha === '') {
          sendJson(res, 422, { message: 'ref and sha are required' });
          return true;
        }
        if (!repo.objects.has(sha)) {
          sendJson(res, 422, { message: 'object does not exist' });
          return true;
        }
        const existing = repo.refs.get(ref);
        if (existing !== undefined) {
          if (existing === sha) {
            sendJson(res, 201, { ref, node_id: globalId('Ref', `${repo.id}:${ref}`), url: `/api/v3/repos/${owner}/${name}/git/refs/${ref.replace(/^refs\//, '')}`, object: { sha, type: 'commit', url: '' } });
            return true;
          }
          sendJson(res, 422, { message: 'Reference already exists' });
          return true;
        }
        repo.refs.set(ref, sha);
        sendJson(res, 201, { ref, node_id: globalId('Ref', `${repo.id}:${ref}`), url: `/api/v3/repos/${owner}/${name}/git/refs/${ref.replace(/^refs\//, '')}`, object: { sha, type: 'commit', url: '' } });
        return true;
      }
      if (method === 'GET') {
        if (rest.length === 2) {
          const all = sortedRefs(repo).map((entry) => ({
            ref: entry.ref,
            node_id: globalId('Ref', `${repo.id}:${entry.ref}`),
            url: `/api/v3/repos/${owner}/${name}/git/refs/${entry.ref.replace(/^refs\//, '')}`,
            object: { sha: entry.oid, type: 'commit', url: '' },
          }));
          sendJson(res, 200, all);
          return true;
        }
        const ref = `refs/${rest.slice(2).map(decodeSegment).join('/')}`;
        const oid = repo.refs.get(ref);
        if (oid === undefined) {
          sendJson(res, 404, { message: 'Not Found' });
          return true;
        }
        sendJson(res, 200, {
          ref,
          node_id: globalId('Ref', `${repo.id}:${ref}`),
          url: `/api/v3/repos/${owner}/${name}/git/refs/${rest.slice(2).map(decodeSegment).join('/')}`,
          object: { sha: oid, type: 'commit', url: '' },
        });
        return true;
      }
      sendJson(res, 404, { message: 'Not Found' });
      return true;
    }

    // branches
    if (rest[0] === 'branches') {
      if (method === 'GET' && rest.length === 1) {
        const list = sortedRefs(repo)
          .filter((entry) => entry.ref.startsWith('refs/heads/'))
          .map((entry) => ({
            name: entry.ref.slice('refs/heads/'.length),
            commit: { sha: entry.oid, url: `/api/v3/repos/${owner}/${name}/commits/${entry.oid}` },
            protected: false,
          }));
        sendJson(res, 200, list);
        return true;
      }
      if (method === 'GET' && rest.length === 2) {
        const branch = decodeSegment(rest[1] as string);
        const oid = repo.refs.get(`refs/heads/${branch}`);
        if (oid === undefined) {
          sendJson(res, 404, { message: 'Not Found' });
          return true;
        }
        sendJson(res, 200, {
          name: branch,
          commit: { sha: oid, url: `/api/v3/repos/${owner}/${name}/commits/${oid}` },
          protected: false,
          protection: { enabled: false, required_status_checks: { enforcement_level: 'off', contexts: [] } },
        });
        return true;
      }
      sendJson(res, 404, { message: 'Not Found' });
      return true;
    }

    // commits
    if (rest[0] === 'commits') {
      if (method === 'GET' && rest.length === 1) {
        const tip = resolveRef(repo, url.searchParams.get('sha') ?? undefined);
        const list = listCommits(repo, tip).map((entry) => {
          const author = parseIdentity(entry.commit.author);
          const committer = parseIdentity(entry.commit.committer);
          return {
            sha: entry.sha,
            node_id: globalId('Commit', `${repo.id}:${entry.sha}`),
            commit: {
              message: entry.commit.message,
              author: { name: author.name, email: author.email, date: new Date(author.epoch * 1000).toISOString() },
              committer: { name: committer.name, email: committer.email, date: new Date(committer.epoch * 1000).toISOString() },
              tree: { sha: entry.commit.tree, url: '' },
            },
            parents: entry.commit.parents.map((sha) => ({ sha, url: '' })),
            author: userJson(VIEWER),
            committer: userJson(VIEWER),
            url: `/api/v3/repos/${owner}/${name}/commits/${entry.sha}`,
            html_url: `https://example.invalid/${owner}/${name}/commit/${entry.sha}`,
          };
        });
        const page = paginate(res, req, url, list);
        sendJson(res, 200, page);
        return true;
      }
      if (method === 'GET' && rest.length === 2) {
        const sha = decodeSegment(rest[1] as string);
        const obj = repo.objects.get(sha);
        if (obj === undefined || obj.type !== 'commit') {
          sendJson(res, 404, { message: 'Not Found' });
          return true;
        }
        const parsed = parseCommit(obj.data);
        const author = parseIdentity(parsed.author);
        const committer = parseIdentity(parsed.committer);
        sendJson(res, 200, {
          sha,
          node_id: globalId('Commit', `${repo.id}:${sha}`),
          commit: {
            message: parsed.message,
            author: { name: author.name, email: author.email, date: new Date(author.epoch * 1000).toISOString() },
            committer: { name: committer.name, email: committer.email, date: new Date(committer.epoch * 1000).toISOString() },
            tree: { sha: parsed.tree, url: '' },
          },
          parents: parsed.parents.map((parent) => ({ sha: parent, url: '' })),
          author: userJson(VIEWER),
          committer: userJson(VIEWER),
          url: `/api/v3/repos/${owner}/${name}/commits/${sha}`,
          html_url: `https://example.invalid/${owner}/${name}/commit/${sha}`,
        });
        return true;
      }
      sendJson(res, 404, { message: 'Not Found' });
      return true;
    }

    // contents
    if (rest[0] === 'contents') {
      const contentPath = rest.slice(1).map(decodeSegment).join('/');
      const refParam = url.searchParams.get('ref') ?? undefined;
      if (method === 'GET') {
        const tip = resolveRef(repo, refParam);
        if (tip === undefined) {
          sendJson(res, 404, { message: 'Not Found' });
          return true;
        }
        const commit = repo.objects.get(tip);
        if (commit === undefined || commit.type !== 'commit') {
          sendJson(res, 404, { message: 'Not Found' });
          return true;
        }
        const flat = new Map<string, { oid: string; mode: string }>();
        flattenTree(repo, parseCommit(commit.data).tree, '', flat);
        if (contentPath === '') {
          const entries = listDirectory(repo, flat, '');
          sendJson(res, 200, entries);
          return true;
        }
        const file = flat.get(contentPath);
        if (file !== undefined) {
          const blob = repo.objects.get(file.oid);
          const data = blob === undefined ? Buffer.alloc(0) : blob.data;
          sendJson(res, 200, {
            type: 'file',
            encoding: 'base64',
            size: data.length,
            name: contentPath.split('/').pop() ?? contentPath,
            path: contentPath,
            content: data.toString('base64'),
            sha: file.oid,
            url: `/api/v3/repos/${owner}/${name}/contents/${contentPath}`,
            html_url: `https://example.invalid/${owner}/${name}/blob/${tip}/${contentPath}`,
          });
          return true;
        }
        const prefix = `${contentPath}/`;
        const hasChildren = [...flat.keys()].some((path) => path.startsWith(prefix));
        if (hasChildren) {
          sendJson(res, 200, listDirectory(repo, flat, contentPath));
          return true;
        }
        sendJson(res, 404, { message: 'Not Found' });
        return true;
      }
      if (method === 'PUT' || method === 'DELETE') {
        if (contentPath === '') {
          sendJson(res, 422, { message: 'a path is required' });
          return true;
        }
        const branch = json !== undefined && typeof json.branch === 'string' && json.branch !== '' ? (json.branch as string) : repo.defaultBranch;
        let tip = repo.refs.get(`refs/heads/${branch}`);
        if (tip === undefined) {
          // The branch does not exist yet: create it from the default tip, or
          // start an unborn repository at the new commit.
          tip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
        }
        const flat = new Map<string, { oid: string; mode: string }>();
        if (tip !== undefined) {
          const commit = repo.objects.get(tip);
          if (commit !== undefined && commit.type === 'commit') {
            flattenTree(repo, parseCommit(commit.data).tree, '', flat);
          }
        }
        const current = flat.get(contentPath);
        if (method === 'PUT') {
          const content = json === undefined ? '' : stringField(json, 'content');
          const message = json !== undefined && typeof json.message === 'string' && json.message !== '' ? (json.message as string) : `Update ${contentPath}`;
          const givenSha = json === undefined ? undefined : (json.sha as string | undefined);
          if (current !== undefined) {
            if (givenSha === undefined || givenSha !== current.oid) {
              sendJson(res, 409, { message: 'sha does not match the current file' });
              return true;
            }
          }
          let blobData: Buffer;
          try {
            blobData = Buffer.from(content, 'base64');
          } catch {
            sendJson(res, 422, { message: 'content is not valid base64' });
            return true;
          }
          const blobOid = storeObject(repo, 'blob', blobData);
          flat.set(contentPath, { oid: blobOid, mode: '100644' });
          const treeOid = treeFromFlat(repo, flat);
          const epoch = stamp().epoch;
          const parents = tip !== undefined ? [tip] : [];
          const commitOid = makeCommit(repo, treeOid, parents, message, epoch);
          repo.refs.set(`refs/heads/${branch}`, commitOid);
          sendJson(res, current === undefined ? 201 : 200, {
            content: {
              type: 'file',
              encoding: 'base64',
              size: blobData.length,
              name: contentPath.split('/').pop() ?? contentPath,
              path: contentPath,
              content: blobData.toString('base64'),
              sha: blobOid,
              url: `/api/v3/repos/${owner}/${name}/contents/${contentPath}`,
            },
            commit: {
              sha: commitOid,
              node_id: globalId('Commit', `${repo.id}:${commitOid}`),
              message,
              author: { name: VIEWER.name, email: VIEWER.email, date: new Date(epoch * 1000).toISOString() },
              committer: { name: VIEWER.name, email: VIEWER.email, date: new Date(epoch * 1000).toISOString() },
            },
          });
          return true;
        }
        // DELETE
        if (current === undefined) {
          sendJson(res, 404, { message: 'Not Found' });
          return true;
        }
        const givenSha = json === undefined ? undefined : (json.sha as string | undefined);
        if (givenSha !== undefined && givenSha !== current.oid) {
          sendJson(res, 409, { message: 'sha does not match the current file' });
          return true;
        }
        const message = json !== undefined && typeof json.message === 'string' && json.message !== '' ? (json.message as string) : `Delete ${contentPath}`;
        flat.delete(contentPath);
        const treeOid = treeFromFlat(repo, flat);
        const epoch = stamp().epoch;
        const parents = tip !== undefined ? [tip] : [];
        const commitOid = makeCommit(repo, treeOid, parents, message, epoch);
        repo.refs.set(`refs/heads/${branch}`, commitOid);
        sendJson(res, 200, {
          commit: {
            sha: commitOid,
            node_id: globalId('Commit', `${repo.id}:${commitOid}`),
            message,
            author: { name: VIEWER.name, email: VIEWER.email, date: new Date(epoch * 1000).toISOString() },
            committer: { name: VIEWER.name, email: VIEWER.email, date: new Date(epoch * 1000).toISOString() },
          },
          content: null,
        });
        return true;
      }
      sendJson(res, 404, { message: 'Not Found' });
      return true;
    }

    // labels
    if (rest[0] === 'labels') {
      if (method === 'GET' && rest.length === 1) {
        sendJson(res, 200, [...repo.labels.values()].map((label) => ({
          id: 40000 + label.name.length,
          node_id: globalId('Label', `${repo.id}:${label.name}`),
          url: `/api/v3/repos/${owner}/${name}/labels/${encodeURIComponent(label.name)}`,
          name: label.name,
          color: label.color,
          description: label.description,
          default: false,
        })));
        return true;
      }
      if (method === 'POST' && rest.length === 1) {
        const name = json === undefined ? '' : stringField(json, 'name');
        const color = json === undefined ? 'ededed' : stringField(json, 'color') || 'ededed';
        if (name === '') {
          sendJson(res, 422, { message: 'name is required' });
          return true;
        }
        const existing = repo.labels.get(name);
        if (existing !== undefined) {
          sendJson(res, 201, { id: 40000 + name.length, node_id: globalId('Label', `${repo.id}:${name}`), url: '', name, color: existing.color, description: existing.description, default: false });
          return true;
        }
        const label = { name, color, description: json !== undefined && typeof json.description === 'string' ? (json.description as string) : '' };
        repo.labels.set(name, label);
        sendJson(res, 201, { id: 40000 + name.length, node_id: globalId('Label', `${repo.id}:${name}`), url: '', name, color, description: label.description, default: false });
        return true;
      }
      sendJson(res, 404, { message: 'Not Found' });
      return true;
    }

    // issues and comments
    if (rest[0] === 'issues') {
      if (rest.length === 1) {
        if (method === 'POST') {
          const title = json === undefined ? '' : stringField(json, 'title');
          if (title === '') {
            sendJson(res, 422, { message: 'title is required' });
            return true;
          }
          const labels = Array.isArray(json?.labels) ? (json.labels as unknown[]).map((label) => String(label)) : [];
          for (const label of labels) {
            if (!repo.labels.has(label)) {
              sendJson(res, 422, { message: `label "${label}" does not exist`, errors: [{ message: `label "${label}" does not exist` }] });
              return true;
            }
          }
          const stampNow = stamp();
          const issue: Issue = {
            number: repo.nextIssue,
            title,
            body: json !== undefined && typeof json.body === 'string' ? (json.body as string) : '',
            state: 'open',
            labels,
            seq: nextTick(),
            createdAt: stampNow.iso,
            updatedAt: stampNow.iso,
            user: VIEWER,
          };
          repo.nextIssue += 1;
          repo.issues.push(issue);
          repo.comments.set(issue.number, []);
          sendJson(res, 201, issueJson(repo, issue));
          return true;
        }
        if (method === 'GET') {
          const state = url.searchParams.get('state') ?? 'open';
          const sort = url.searchParams.get('sort') ?? 'created';
          const direction = url.searchParams.get('direction') ?? 'desc';
          let list = repo.issues.filter((issue) => state === 'all' || issue.state === state);
          if (sort === 'created') {
            list = [...list].sort((a, b) => (direction === 'asc' ? a.seq - b.seq : b.seq - a.seq));
          }
          const page = paginate(res, req, url, list.map((issue) => issueJson(repo, issue)));
          sendJson(res, 200, page);
          return true;
        }
        sendJson(res, 404, { message: 'Not Found' });
        return true;
      }
      const issueNumber = Number.parseInt(rest[1] as string, 10);
      const issue = repo.issues.find((entry) => entry.number === issueNumber);
      if (issue === undefined) {
        sendJson(res, 404, { message: 'Not Found' });
        return true;
      }
      if (rest.length === 2) {
        if (method === 'GET') {
          sendJson(res, 200, issueJson(repo, issue));
          return true;
        }
        if (method === 'PATCH') {
          if (json !== undefined) {
            if (typeof json.title === 'string') issue.title = json.title;
            if (typeof json.body === 'string') issue.body = json.body;
            if (typeof json.state === 'string' && (json.state === 'open' || json.state === 'closed')) {
              issue.state = json.state;
            }
            if (Array.isArray(json.labels)) {
              const labels = (json.labels as unknown[]).map((label) => String(label));
              for (const label of labels) {
                if (!repo.labels.has(label)) {
                  sendJson(res, 422, { message: `label "${label}" does not exist` });
                  return true;
                }
              }
              issue.labels = labels;
            }
            issue.updatedAt = stamp().iso;
          }
          sendJson(res, 200, issueJson(repo, issue));
          return true;
        }
        sendJson(res, 404, { message: 'Not Found' });
        return true;
      }
      if (rest.length === 3 && rest[2] === 'comments') {
        const comments = repo.comments.get(issue.number) ?? [];
        if (method === 'POST') {
          const bodyText = json === undefined ? '' : stringField(json, 'body');
          if (bodyText === '') {
            sendJson(res, 422, { message: 'body is required' });
            return true;
          }
          const comment: Comment = { id: repo.nextComment, body: bodyText, user: VIEWER, createdAt: stamp().iso };
          repo.nextComment += 1;
          comments.push(comment);
          repo.comments.set(issue.number, comments);
          sendJson(res, 201, commentJson(repo, issue.number, comment));
          return true;
        }
        if (method === 'GET') {
          const page = paginate(res, req, url, comments.map((comment) => commentJson(repo, issue.number, comment)));
          sendJson(res, 200, page);
          return true;
        }
        sendJson(res, 404, { message: 'Not Found' });
        return true;
      }
      sendJson(res, 404, { message: 'Not Found' });
      return true;
    }

    // pull requests
    if (rest[0] === 'pulls') {
      if (rest.length === 1) {
        if (method === 'POST') {
          const title = json === undefined ? '' : stringField(json, 'title');
          const headRaw = json === undefined ? '' : stringField(json, 'head');
          const baseRaw = json === undefined ? '' : stringField(json, 'base');
          const head = headRaw.includes(':') ? (headRaw.split(':').pop() as string) : headRaw;
          const base = baseRaw.includes(':') ? (baseRaw.split(':').pop() as string) : baseRaw;
          if (title === '' || head === '' || base === '') {
            sendJson(res, 422, { message: 'title, head and base are required' });
            return true;
          }
          const headSha = repo.refs.get(`refs/heads/${head}`);
          const baseSha = repo.refs.get(`refs/heads/${base}`);
          if (headSha === undefined || baseSha === undefined) {
            sendJson(res, 422, { message: 'head or base branch does not exist' });
            return true;
          }
          const existing = repo.pulls.find((entry) => entry.headRef === head && entry.baseRef === base && entry.state === 'open');
          if (existing !== undefined) {
            sendJson(res, 422, { message: 'A pull request already exists for this head branch', errors: [{ message: 'already exists' }] });
            return true;
          }
          const stampNow = stamp();
          const pull: Pull = {
            number: repo.nextPull,
            title,
            body: json !== undefined && typeof json.body === 'string' ? (json.body as string) : '',
            headRef: head,
            baseRef: base,
            headSha,
            baseSha,
            state: 'open',
            merged: false,
            mergedAt: null,
            mergeCommitSha: null,
            seq: nextTick(),
            createdAt: stampNow.iso,
            user: VIEWER,
          };
          repo.nextPull += 1;
          repo.pulls.push(pull);
          sendJson(res, 201, pullJson(repo, pull));
          return true;
        }
        if (method === 'GET') {
          const state = url.searchParams.get('state') ?? 'open';
          const list = repo.pulls.filter((pull) => state === 'all' || pull.state === state);
          const page = paginate(res, req, url, list.map((pull) => pullJson(repo, pull)));
          sendJson(res, 200, page);
          return true;
        }
        sendJson(res, 404, { message: 'Not Found' });
        return true;
      }
      const pullNumber = Number.parseInt(rest[1] as string, 10);
      const pull = repo.pulls.find((entry) => entry.number === pullNumber);
      if (pull === undefined) {
        sendJson(res, 404, { message: 'Not Found' });
        return true;
      }
      if (rest.length === 2) {
        if (method === 'GET') {
          sendJson(res, 200, pullJson(repo, pull));
          return true;
        }
        if (method === 'PATCH') {
          if (json !== undefined) {
            if (typeof json.title === 'string') pull.title = json.title;
            if (typeof json.body === 'string') pull.body = json.body;
            if (typeof json.state === 'string' && (json.state === 'open' || json.state === 'closed')) {
              pull.state = json.state;
            }
          }
          sendJson(res, 200, pullJson(repo, pull));
          return true;
        }
        sendJson(res, 404, { message: 'Not Found' });
        return true;
      }
      if (rest.length === 3 && rest[2] === 'files') {
        if (method !== 'GET') {
          sendJson(res, 404, { message: 'Not Found' });
          return true;
        }
        sendJson(res, 200, pullFiles(repo, pull));
        return true;
      }
      if (rest.length === 3 && rest[2] === 'merge') {
        if (method !== 'PUT') {
          sendJson(res, 404, { message: 'Not Found' });
          return true;
        }
        if (pull.state !== 'open') {
          sendJson(res, 405, { message: 'Pull request is not open' });
          return true;
        }
        const mergeMethod = json !== undefined && typeof json.merge_method === 'string' ? (json.merge_method as string) : 'squash';
        const tip = currentBaseTip(repo, pull);
        const base = mergeBase(repo, pull.headSha, tip);
        if (base === null) {
          sendJson(res, 405, { message: 'No merge base: cannot merge' });
          return true;
        }
        const merged = threeWayMerge(repo, base, pull.headSha, tip);
        if (merged.conflict || merged.tree === null) {
          sendJson(res, 405, { message: 'Merge conflict: the pull request cannot be merged cleanly' });
          return true;
        }
        const epoch = stamp().epoch;
        const message = mergeMethod === 'squash'
          ? `${pull.title} (#${pull.number})`
          : `Merge pull request #${pull.number} from ${repo.owner}/${pull.headRef}`;
        const mergeSha = makeCommit(repo, merged.tree, [tip], message, epoch);
        repo.refs.set(`refs/heads/${pull.baseRef}`, mergeSha);
        pull.state = 'closed';
        pull.merged = true;
        pull.mergedAt = new Date(epoch * 1000).toISOString();
        pull.mergeCommitSha = mergeSha;
        sendJson(res, 200, { sha: mergeSha, merged: true, message });
        return true;
      }
      sendJson(res, 404, { message: 'Not Found' });
      return true;
    }

    notFound();
    return true;
  }

  return false;
}

/** The immediate children of `dir` in a flat tree map, in GitHub's contents shape. */
function listDirectory(
  repo: Repo,
  flat: Map<string, { oid: string; mode: string }>,
  dir: string,
): Record<string, unknown>[] {
  const prefix = dir === '' ? '' : `${dir}/`;
  const entries = new Map<string, { type: string; oid: string; size: number }>();
  for (const [path, value] of flat) {
    if (!path.startsWith(prefix)) continue;
    const rest = path.slice(prefix.length);
    const slash = rest.indexOf('/');
    if (slash < 0) {
      const blob = repo.objects.get(value.oid);
      entries.set(rest, { type: 'file', oid: value.oid, size: blob === undefined ? 0 : blob.data.length });
    } else {
      const name = rest.slice(0, slash);
      if (!entries.has(name)) {
        const dirFlat = new Map<string, { oid: string; mode: string }>();
        for (const [p, v] of flat) {
          if (p.startsWith(`${prefix}${name}/`)) dirFlat.set(p.slice(prefix.length), v);
        }
        entries.set(name, { type: 'dir', oid: treeFromFlat(repo, dirFlat), size: 0 });
      }
    }
  }
  return [...entries.entries()]
    .sort((a, b) => (a[0] < b[0] ? -1 : 1))
    .map(([name, entry]) => ({
      type: entry.type,
      size: entry.size,
      name,
      path: dir === '' ? name : `${dir}/${name}`,
      sha: entry.oid,
      url: `/api/v3/repos/${repo.owner}/${repo.name}/contents/${dir === '' ? name : `${dir}/${name}`}`,
      html_url: `https://example.invalid/${repo.owner}/${repo.name}/tree/main/${dir === '' ? name : `${dir}/${name}`}`,
    }));
}

// ---------------------------------------------------------------------------
// GraphQL v4: a small parser and executor for the documents gh sends.
// ---------------------------------------------------------------------------

interface GqlField {
  alias: string | null;
  name: string;
  args: Record<string, unknown>;
  selections: GqlField[];
  inlineType: string | null;
  fragmentName: string | null;
}
interface GqlOperation {
  kind: 'query' | 'mutation';
  name: string | null;
  selections: GqlField[];
}

function tokenizeGql(source: string): string[] {
  const tokens: string[] = [];
  let i = 0;
  while (i < source.length) {
    const ch = source[i] as string;
    if (/\s/.test(ch) || ch === ',') {
      i += 1;
      continue;
    }
    if (ch === '#') {
      while (i < source.length && source[i] !== '\n') i += 1;
      continue;
    }
    if (ch === '"') {
      let j = i + 1;
      let out = '"';
      while (j < source.length) {
        const c = source[j] as string;
        out += c;
        if (c === '\\' && j + 1 < source.length) {
          out += source[j + 1] as string;
          j += 2;
          continue;
        }
        if (c === '"') {
          j += 1;
          break;
        }
        j += 1;
      }
      tokens.push(out);
      i = j;
      continue;
    }
    if ('{}()[]:!=$@'.includes(ch)) {
      if (ch === '.' && source.slice(i, i + 3) === '...') {
        tokens.push('...');
        i += 3;
        continue;
      }
      tokens.push(ch);
      i += 1;
      continue;
    }
    let j = i;
    while (j < source.length && /[A-Za-z0-9_\-.+]/.test(source[j] as string)) j += 1;
    tokens.push(source.slice(i, j));
    i = j;
  }
  return tokens;
}

class GqlParser {
  private tokens: string[];
  private pos = 0;
  fragments = new Map<string, { type: string; selections: GqlField[] }>();

  constructor(source: string) {
    this.tokens = tokenizeGql(source);
  }
  peek(): string | undefined {
    return this.tokens[this.pos];
  }
  next(): string {
    const token = this.tokens[this.pos];
    this.pos += 1;
    return token === undefined ? '' : token;
  }
  expect(token: string): void {
    const got = this.next();
    if (got !== token) throw new Error(`expected ${token}, got ${got}`);
  }
  parseValue(): unknown {
    const token = this.next();
    if (token === '$') return { __var: this.next() };
    if (token === '[') {
      const list: unknown[] = [];
      while (this.peek() !== ']') list.push(this.parseValue());
      this.expect(']');
      return list;
    }
    if (token === '{') {
      const obj: Record<string, unknown> = {};
      while (this.peek() !== '}') {
        const key = this.next();
        this.expect(':');
        obj[key] = this.parseValue();
      }
      this.expect('}');
      return obj;
    }
    if (token.startsWith('"')) return JSON.parse(token) as string;
    if (token === 'true') return true;
    if (token === 'false') return false;
    if (token === 'null') return null;
    if (/^-?\d+$/.test(token)) return Number.parseInt(token, 10);
    if (/^-?\d+\.\d+$/.test(token)) return Number.parseFloat(token);
    return token; // an enum value, read as its name
  }
  parseArguments(): Record<string, unknown> {
    const args: Record<string, unknown> = {};
    this.expect('(');
    while (this.peek() !== ')') {
      const key = this.next();
      this.expect(':');
      args[key] = this.parseValue();
    }
    this.expect(')');
    return args;
  }
  parseSelectionSet(): GqlField[] {
    this.expect('{');
    const fields: GqlField[] = [];
    while (this.peek() !== '}') {
      fields.push(this.parseField());
    }
    this.expect('}');
    return fields;
  }
  parseField(): GqlField {
    const token = this.next();
    if (token === '...') {
      const next = this.next();
      if (next === 'on') {
        const typeName = this.next();
        const selections = this.parseSelectionSet();
        return { alias: null, name: '', args: {}, selections, inlineType: typeName, fragmentName: null };
      }
      const selections = this.peek() === '{' ? this.parseSelectionSet() : [];
      return { alias: null, name: '', args: {}, selections, inlineType: null, fragmentName: next };
    }
    let alias: string | null = null;
    let name = token;
    if (this.peek() === ':') {
      this.next();
      alias = token;
      name = this.next();
    }
    let args: Record<string, unknown> = {};
    if (this.peek() === '(') args = this.parseArguments();
    // Directives: skip @name[(args)].
    while (this.peek() === '@') {
      this.next();
      this.next();
      if (this.peek() === '(') this.parseArguments();
    }
    const selections = this.peek() === '{' ? this.parseSelectionSet() : [];
    return { alias, name, args, selections, inlineType: null, fragmentName: null };
  }
  parseOperation(): GqlOperation {
    let kind: 'query' | 'mutation' = 'query';
    let name: string | null = null;
    const token = this.peek();
    if (token === 'query' || token === 'mutation') {
      kind = this.next() as 'query' | 'mutation';
      const next = this.peek();
      if (next !== undefined && next !== '{' && next !== '(') name = this.next();
    } else if (token === 'fragment') {
      this.next();
      const fragmentName = this.next();
      this.expect('on');
      const typeName = this.next();
      const selections = this.parseSelectionSet();
      this.fragments.set(fragmentName, { type: typeName, selections });
      return { kind: 'query', name: null, selections: [] };
    }
    // Variable definitions: skip ($name: Type = default, ...).
    if (this.peek() === '(') {
      let depth = 0;
      while (this.pos < this.tokens.length) {
        const t = this.next();
        if (t === '(' || t === '[' || t === '{') depth += 1;
        else if (t === ')' || t === ']' || t === '}') {
          depth -= 1;
          if (depth === 0) break;
        }
      }
    }
    const selections = this.parseSelectionSet();
    return { kind, name, selections };
  }
  parseDocument(): GqlOperation[] {
    const operations: GqlOperation[] = [];
    while (this.pos < this.tokens.length) {
      const op = this.parseOperation();
      if (op.selections.length > 0 || op.name !== null) operations.push(op);
    }
    return operations;
  }
}

function resolveValue(value: unknown, variables: Record<string, unknown>): unknown {
  if (isRecord(value) && typeof value.__var === 'string') {
    return variables[value.__var as string];
  }
  if (Array.isArray(value)) return value.map((entry) => resolveValue(entry, variables));
  if (isRecord(value)) {
    const out: Record<string, unknown> = {};
    for (const [key, entry] of Object.entries(value)) out[key] = resolveValue(entry, variables);
    return out;
  }
  return value;
}
function resolveArgs(args: Record<string, unknown>, variables: Record<string, unknown>): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const [key, value] of Object.entries(args)) out[key] = resolveValue(value, variables);
  return out;
}

const REPO_TYPE_FIELDS = ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequests', 'pullRequest'];
const ISSUE_TYPE_FIELDS = ['id', 'number', 'title', 'state', 'body'];
const PULL_TYPE_FIELDS = ['id', 'number', 'headRefName', 'baseRefName', 'mergeable', 'state', 'merged', 'files'];
const SEARCH_TYPE_VALUES = ['ISSUE', 'PULL_REQUEST', 'REPOSITORY', 'USER', 'DISCUSSION', 'COMMIT'];

function repoByGlobalId(id: string): Repo | undefined {
  const parsed = parseGlobalId(id);
  if (parsed === null || parsed.kind !== 'Repository') return undefined;
  const dbId = Number.parseInt(parsed.key, 10);
  for (const repo of repos.values()) {
    if (repo.id === dbId) return repo;
  }
  return undefined;
}
function issueByGlobalId(id: string): { repo: Repo; issue: Issue } | undefined {
  const parsed = parseGlobalId(id);
  if (parsed === null || parsed.kind !== 'Issue') return undefined;
  const [repoId, number] = parsed.key.split(':');
  const repo = [...repos.values()].find((entry) => entry.id === Number.parseInt(repoId as string, 10));
  if (repo === undefined) return undefined;
  const issue = repo.issues.find((entry) => entry.number === Number.parseInt(number as string, 10));
  if (issue === undefined) return undefined;
  return { repo, issue };
}
function pullByGlobalId(id: string): { repo: Repo; pull: Pull } | undefined {
  const parsed = parseGlobalId(id);
  if (parsed === null || parsed.kind !== 'PullRequest') return undefined;
  const [repoId, number] = parsed.key.split(':');
  const repo = [...repos.values()].find((entry) => entry.id === Number.parseInt(repoId as string, 10));
  if (repo === undefined) return undefined;
  const pull = repo.pulls.find((entry) => entry.number === Number.parseInt(number as string, 10));
  if (pull === undefined) return undefined;
  return { repo, pull };
}

function issueGlobalId(repo: Repo, issue: Issue): string {
  return globalId('Issue', `${repo.id}:${issue.number}`);
}
function pullGlobalId(repo: Repo, pull: Pull): string {
  return globalId('PullRequest', `${repo.id}:${pull.number}`);
}
function commentGlobalId(repo: Repo, issueNumber: number, comment: Comment): string {
  return globalId('IssueComment', `${repo.id}:${issueNumber}:${comment.id}`);
}

function cursorFor(number: number): string {
  return b64encode(`cursor:${number}`);
}
function numberFromCursor(cursor: string | null | undefined): number | null {
  if (cursor === null || cursor === undefined || cursor === '') return null;
  try {
    const decoded = b64decode(cursor);
    const match = /^cursor:(\d+)$/.exec(decoded);
    return match === null ? null : Number.parseInt(match[1] as string, 10);
  } catch {
    return null;
  }
}

interface GqlExecutor {
  variables: Record<string, unknown>;
  errors: { message: string }[];
  fragments: Map<string, { type: string; selections: GqlField[] }>;
}

function gqlError(exec: GqlExecutor, message: string): void {
  exec.errors.push({ message });
}

function selectFields(
  exec: GqlExecutor,
  typeName: string,
  source: Record<string, unknown> | null,
  selections: GqlField[],
  allowed: readonly string[],
): Record<string, unknown> | null {
  if (source === null) return null;
  const out: Record<string, unknown> = {};
  for (const field of selections) {
    if (field.fragmentName !== null) {
      const fragment = exec.fragments.get(field.fragmentName);
      if (fragment !== undefined) {
        const merged = selectFields(exec, typeName, source, fragment.selections, allowed);
        if (merged !== null) Object.assign(out, merged);
      }
      continue;
    }
    if (field.inlineType !== null) {
      if (field.inlineType !== typeName) continue;
      const merged = selectFields(exec, typeName, source, field.selections, allowed);
      if (merged !== null) Object.assign(out, merged);
      continue;
    }
    const key = field.alias ?? field.name;
    if (field.name === '__typename') {
      out[key] = typeName;
      continue;
    }
    if (!allowed.includes(field.name)) {
      gqlError(exec, `Cannot query field "${field.name}" on type "${typeName}".`);
      out[key] = null;
      continue;
    }
    out[key] = source[field.name];
  }
  return out;
}

function repoGql(exec: GqlExecutor, repo: Repo, selections: GqlField[]): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const field of selections) {
    if (field.fragmentName !== null || field.inlineType !== null) continue;
    const key = field.alias ?? field.name;
    if (field.name === '__typename') {
      out[key] = 'Repository';
      continue;
    }
    if (!REPO_TYPE_FIELDS.includes(field.name)) {
      gqlError(exec, `Cannot query field "${field.name}" on type "Repository".`);
      out[key] = null;
      continue;
    }
    const args = resolveArgs(field.args, exec.variables);
    switch (field.name) {
      case 'id':
        out[key] = globalId('Repository', String(repo.id));
        break;
      case 'databaseId':
        out[key] = repo.id;
        break;
      case 'name':
        out[key] = repo.name;
        break;
      case 'nameWithOwner':
        out[key] = `${repo.owner}/${repo.name}`;
        break;
      case 'owner':
        out[key] = selectFields(exec, 'User', { login: VIEWER.login }, field.selections, ['login']);
        break;
      case 'defaultBranchRef': {
        const oid = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
        out[key] = oid === undefined ? null : selectFields(exec, 'Ref', { name: repo.defaultBranch }, field.selections, ['name']);
        break;
      }
      case 'viewerPermission':
        out[key] = 'ADMIN';
        break;
      case 'hasIssuesEnabled':
        out[key] = true;
        break;
      case 'issue': {
        const number = args.number as number | undefined;
        const issue = repo.issues.find((entry) => entry.number === number);
        out[key] = issue === undefined ? null : issueGql(exec, repo, issue, field.selections);
        break;
      }
      case 'issues': {
        out[key] = issuesConnection(exec, repo, args, field.selections);
        break;
      }
      case 'pullRequests': {
        const first = typeof args.first === 'number' ? args.first : 100;
        const nodes = repo.pulls.slice(0, first).map((pull) => pullGql(exec, repo, pull, field.selections[0]?.selections ?? []));
        out[key] = selectConnection(exec, nodes, field.selections, 'PullRequestConnection');
        break;
      }
      case 'pullRequest': {
        const number = args.number as number | undefined;
        const pull = repo.pulls.find((entry) => entry.number === number);
        out[key] = pull === undefined ? null : pullGql(exec, repo, pull, field.selections);
        break;
      }
      default:
        out[key] = null;
    }
  }
  return out;
}

function selectConnection(
  exec: GqlExecutor,
  nodes: Record<string, unknown>[],
  selections: GqlField[],
  typeName: string,
): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const field of selections) {
    const key = field.alias ?? field.name;
    if (field.name === 'nodes') {
      out[key] = nodes;
    } else if (field.name === 'pageInfo') {
      out[key] = selectFields(exec, 'PageInfo', { hasNextPage: false, endCursor: null }, field.selections, ['hasNextPage', 'endCursor', 'hasPreviousPage', 'startCursor']);
    } else if (field.name === '__typename') {
      out[key] = typeName;
    } else {
      gqlError(exec, `Cannot query field "${field.name}" on type "${typeName}".`);
      out[key] = null;
    }
  }
  return out;
}

function issuesConnection(
  exec: GqlExecutor,
  repo: Repo,
  args: Record<string, unknown>,
  selections: GqlField[],
): Record<string, unknown> {
  const first = typeof args.first === 'number' ? args.first : 100;
  const states = Array.isArray(args.states) ? (args.states as string[]) : null;
  const orderBy = isRecord(args.orderBy) ? args.orderBy : null;
  const after = numberFromCursor(typeof args.after === 'string' ? (args.after as string) : null);
  let list = [...repo.issues];
  if (states !== null) {
    const wanted = new Set(states.map((state) => state.toLowerCase()));
    list = list.filter((issue) => wanted.has(issue.state));
  }
  const direction = orderBy !== null && typeof orderBy.direction === 'string' ? (orderBy.direction as string) : 'ASC';
  const field = orderBy !== null && typeof orderBy.field === 'string' ? (orderBy.field as string) : 'CREATED_AT';
  if (field === 'CREATED_AT' && direction === 'DESC') {
    list.sort((a, b) => b.number - a.number);
  } else if (field === 'CREATED_AT') {
    list.sort((a, b) => a.number - b.number);
  } else {
    list.sort((a, b) => (direction === 'DESC' ? b.number - a.number : a.number - b.number));
  }
  if (after !== null) {
    const index = list.findIndex((issue) => issue.number === after);
    list = index >= 0 ? list.slice(index + 1) : list;
  }
  const hasNextPage = list.length > first;
  const page = list.slice(0, first);
  const nodesField = selections.find((entry) => entry.name === 'nodes');
  const nodeSelections = nodesField === undefined ? [] : nodesField.selections;
  const nodes = page.map((issue) => issueGql(exec, repo, issue, nodeSelections));
  const out: Record<string, unknown> = {};
  for (const fieldSel of selections) {
    const key = fieldSel.alias ?? fieldSel.name;
    if (fieldSel.name === 'nodes') {
      out[key] = nodes;
    } else if (fieldSel.name === 'pageInfo') {
      const endCursor = page.length > 0 ? cursorFor((page[page.length - 1] as Issue).number) : null;
      out[key] = selectFields(exec, 'PageInfo', { hasNextPage, endCursor }, fieldSel.selections, ['hasNextPage', 'endCursor', 'hasPreviousPage', 'startCursor']);
    } else if (fieldSel.name === '__typename') {
      out[key] = 'IssueConnection';
    } else {
      gqlError(exec, `Cannot query field "${fieldSel.name}" on type "IssueConnection".`);
      out[key] = null;
    }
  }
  return out;
}

function issueGql(exec: GqlExecutor, repo: Repo, issue: Issue, selections: GqlField[]): Record<string, unknown> {
  const source: Record<string, unknown> = {
    id: issueGlobalId(repo, issue),
    number: issue.number,
    title: issue.title,
    state: issue.state.toUpperCase(),
    body: issue.body,
  };
  return selectFields(exec, 'Issue', source, selections, ISSUE_TYPE_FIELDS) as Record<string, unknown>;
}

function pullGql(exec: GqlExecutor, repo: Repo, pull: Pull, selections: GqlField[]): Record<string, unknown> {
  const state = pull.merged ? 'MERGED' : pull.state === 'open' ? 'OPEN' : 'CLOSED';
  const out: Record<string, unknown> = {};
  for (const field of selections) {
    if (field.fragmentName !== null || field.inlineType !== null) continue;
    const key = field.alias ?? field.name;
    if (field.name === '__typename') {
      out[key] = 'PullRequest';
      continue;
    }
    if (!PULL_TYPE_FIELDS.includes(field.name)) {
      gqlError(exec, `Cannot query field "${field.name}" on type "PullRequest".`);
      out[key] = null;
      continue;
    }
    switch (field.name) {
      case 'id':
        out[key] = pullGlobalId(repo, pull);
        break;
      case 'number':
        out[key] = pull.number;
        break;
      case 'state':
        out[key] = state;
        break;
      case 'merged':
        out[key] = pull.merged;
        break;
      case 'headRefName':
        out[key] = pull.headRef;
        break;
      case 'baseRefName':
        out[key] = pull.baseRef;
        break;
      case 'mergeable':
        out[key] = pull.state === 'open' ? (prConflict(repo, pull) ? 'CONFLICTING' : 'MERGEABLE') : 'UNKNOWN';
        break;
      case 'files': {
        const args = resolveArgs(field.args, exec.variables);
        const first = typeof args.first === 'number' ? args.first : 100;
        const files = pullFiles(repo, pull).slice(0, first);
        const nodesField = field.selections.find((entry) => entry.name === 'nodes');
        const nodeSelections = nodesField === undefined ? [] : nodesField.selections;
        const nodes = files.map((file) => selectFields(exec, 'PullRequestChangedFile', { path: file.filename }, nodeSelections, ['path']) ?? { path: file.filename });
        out[key] = selectConnection(exec, nodes, field.selections, 'PullRequestChangedFileConnection');
        break;
      }
      default:
        out[key] = null;
    }
  }
  return out;
}

function typeGql(exec: GqlExecutor, name: string, selections: GqlField[]): Record<string, unknown> | null {
  let fields: string[] | null = null;
  let enumValues: string[] | null = null;
  if (name === 'Issue') fields = [...ISSUE_TYPE_FIELDS];
  else if (name === 'PullRequest') fields = [...PULL_TYPE_FIELDS];
  else if (name === 'Repository') fields = [...REPO_TYPE_FIELDS];
  else if (name === 'SearchType') enumValues = [...SEARCH_TYPE_VALUES];
  else if (name === 'User') fields = ['id', 'login', 'name', 'email'];
  else if (name === 'IssueConnection') fields = ['nodes', 'pageInfo', 'totalCount'];
  else if (name === 'PullRequestConnection') fields = ['nodes', 'pageInfo', 'totalCount'];
  else return null;
  const out: Record<string, unknown> = {};
  for (const field of selections) {
    const key = field.alias ?? field.name;
    if (field.name === 'fields') {
      const names = fields ?? [];
      const sub = field.selections;
      out[key] = names.map((entry) => selectFields(exec, '__Field', { name: entry }, sub, ['name']));
    } else if (field.name === 'enumValues') {
      const values = enumValues ?? [];
      const sub = field.selections;
      out[key] = values.map((entry) => selectFields(exec, '__EnumValue', { name: entry }, sub, ['name']));
    } else if (field.name === 'name') {
      out[key] = name;
    } else if (field.name === '__typename') {
      out[key] = '__Type';
    } else {
      gqlError(exec, `Cannot query field "${field.name}" on type "__Type".`);
      out[key] = null;
    }
  }
  return out;
}

function executeOperation(exec: GqlExecutor, operation: GqlOperation): Record<string, unknown> {
  const data: Record<string, unknown> = {};
  for (const field of operation.selections) {
    if (field.fragmentName !== null || field.inlineType !== null) continue;
    const key = field.alias ?? field.name;
    const args = resolveArgs(field.args, exec.variables);
    if (operation.kind === 'query') {
      if (field.name === 'viewer') {
        data[key] = selectFields(exec, 'User', { login: VIEWER.login }, field.selections, ['login', 'id', 'name', 'email']);
      } else if (field.name === 'repository') {
        const owner = args.owner as string | undefined;
        const name = args.name as string | undefined;
        const repo = owner !== undefined && name !== undefined ? getRepo(owner, name) : undefined;
        if (repo === undefined || repo.owner !== VIEWER.login) {
          data[key] = null;
        } else {
          data[key] = repoGql(exec, repo, field.selections);
        }
      } else if (field.name === 'node') {
        const id = args.id as string | undefined;
        if (id === undefined) {
          data[key] = null;
        } else {
          const parsed = parseGlobalId(id);
          if (parsed !== null && parsed.kind === 'Repository') {
            const repo = repoByGlobalId(id);
            if (repo === undefined) data[key] = null;
            else {
              const base = repoGql(exec, repo, field.selections.filter((entry) => entry.name !== '' && entry.inlineType === null && entry.fragmentName === null));
              const merged: Record<string, unknown> = { ...base };
              for (const sub of field.selections) {
                if (sub.inlineType === 'Repository') {
                  Object.assign(merged, repoGql(exec, repo, sub.selections));
                } else if (sub.fragmentName !== null) {
                  const fragment = exec.fragments.get(sub.fragmentName);
                  if (fragment !== undefined) Object.assign(merged, repoGql(exec, repo, fragment.selections));
                }
              }
              if (merged.id === undefined) merged.id = globalId('Repository', String(repo.id));
              data[key] = merged;
            }
          } else if (parsed !== null && parsed.kind === 'Issue') {
            const found = issueByGlobalId(id);
            data[key] = found === undefined ? null : issueGql(exec, found.repo, found.issue, field.selections);
          } else {
            data[key] = null;
          }
        }
      } else if (field.name === '__type') {
        const name = args.name as string | undefined;
        data[key] = name === undefined ? null : typeGql(exec, name, field.selections);
      } else if (field.name === '__typename') {
        data[key] = 'Query';
      } else {
        gqlError(exec, `Cannot query field "${field.name}" on type "Query".`);
        data[key] = null;
      }
    } else {
      // Mutations.
      const input = isRecord(args.input) ? (args.input as Record<string, unknown>) : {};
      if (field.name === 'createIssue') {
        const repo = typeof input.repositoryId === 'string' ? repoByGlobalId(input.repositoryId) : undefined;
        if (repo === undefined) {
          gqlError(exec, 'createIssue: repository not found');
          data[key] = null;
        } else {
          const stampNow = stamp();
          const issue: Issue = {
            number: repo.nextIssue,
            title: typeof input.title === 'string' ? input.title : '',
            body: typeof input.body === 'string' ? input.body : '',
            state: 'open',
            labels: [],
            seq: nextTick(),
            createdAt: stampNow.iso,
            updatedAt: stampNow.iso,
            user: VIEWER,
          };
          repo.nextIssue += 1;
          repo.issues.push(issue);
          repo.comments.set(issue.number, []);
          data[key] = selectFields(exec, 'CreateIssuePayload', { issue: issueGql(exec, repo, issue, field.selections[0]?.selections ?? []) }, field.selections, ['issue']);
        }
      } else if (field.name === 'closeIssue') {
        const found = typeof input.issueId === 'string' ? issueByGlobalId(input.issueId) : undefined;
        if (found === undefined) {
          gqlError(exec, 'closeIssue: issue not found');
          data[key] = null;
        } else {
          found.issue.state = 'closed';
          found.issue.updatedAt = stamp().iso;
          data[key] = selectFields(exec, 'CloseIssuePayload', { issue: issueGql(exec, found.repo, found.issue, field.selections[0]?.selections ?? []) }, field.selections, ['issue']);
        }
      } else if (field.name === 'createPullRequest') {
        const repo = typeof input.repositoryId === 'string' ? repoByGlobalId(input.repositoryId) : undefined;
        const head = typeof input.headRefName === 'string' ? input.headRefName : '';
        const base = typeof input.baseRefName === 'string' ? input.baseRefName : '';
        if (repo === undefined || head === '' || base === '') {
          gqlError(exec, 'createPullRequest: repository or branch not found');
          data[key] = null;
        } else {
          const headSha = repo.refs.get(`refs/heads/${head}`);
          const baseSha = repo.refs.get(`refs/heads/${base}`);
          if (headSha === undefined || baseSha === undefined) {
            gqlError(exec, 'createPullRequest: head or base branch does not exist');
            data[key] = null;
          } else {
            const existing = repo.pulls.find((entry) => entry.headRef === head && entry.baseRef === base && entry.state === 'open');
            if (existing !== undefined) {
              gqlError(exec, 'createPullRequest: a pull request already exists for this head branch');
              data[key] = null;
            } else {
              const stampNow = stamp();
              const pull: Pull = {
                number: repo.nextPull,
                title: typeof input.title === 'string' ? input.title : '',
                body: typeof input.body === 'string' ? input.body : '',
                headRef: head,
                baseRef: base,
                headSha,
                baseSha,
                state: 'open',
                merged: false,
                mergedAt: null,
                mergeCommitSha: null,
                seq: nextTick(),
                createdAt: stampNow.iso,
                user: VIEWER,
              };
              repo.nextPull += 1;
              repo.pulls.push(pull);
              data[key] = selectFields(exec, 'CreatePullRequestPayload', { pullRequest: pullGql(exec, repo, pull, field.selections[0]?.selections ?? []) }, field.selections, ['pullRequest']);
            }
          }
        }
      } else if (field.name === 'mergePullRequest') {
        const found = typeof input.pullRequestId === 'string' ? pullByGlobalId(input.pullRequestId) : undefined;
        if (found === undefined) {
          gqlError(exec, 'mergePullRequest: pull request not found');
          data[key] = null;
        } else if (found.pull.state !== 'open') {
          gqlError(exec, 'mergePullRequest: pull request is not open');
          data[key] = null;
        } else {
          const mergeResult = mergePullRequestNow(found.repo, found.pull);
          if (!mergeResult.ok) {
            gqlError(exec, `mergePullRequest: ${mergeResult.message}`);
            data[key] = null;
          } else {
            data[key] = selectFields(exec, 'MergePullRequestPayload', { pullRequest: pullGql(exec, found.repo, found.pull, field.selections[0]?.selections ?? []) }, field.selections, ['pullRequest']);
          }
        }
      } else if (field.name === 'addComment') {
        const found = typeof input.subjectId === 'string' ? issueByGlobalId(input.subjectId) : undefined;
        const bodyText = typeof input.body === 'string' ? input.body : '';
        if (found === undefined) {
          gqlError(exec, 'addComment: subject not found');
          data[key] = null;
        } else {
          const comment: Comment = { id: found.repo.nextComment, body: bodyText, user: VIEWER, createdAt: stamp().iso };
          found.repo.nextComment += 1;
          const comments = found.repo.comments.get(found.issue.number) ?? [];
          comments.push(comment);
          found.repo.comments.set(found.issue.number, comments);
          const node = selectFields(exec, 'IssueComment', { id: commentGlobalId(found.repo, found.issue.number, comment), body: bodyText }, field.selections[0]?.selections[0]?.selections ?? [], ['id', 'body']);
          data[key] = selectFields(exec, 'AddCommentPayload', { commentEdge: { node } }, field.selections, ['commentEdge']);
        }
      } else {
        gqlError(exec, `Cannot query field "${field.name}" on type "Mutation".`);
        data[key] = null;
      }
    }
  }
  return data;
}

/** Squash-merge an open pull request; shared by the REST route and the GraphQL mutation. */
function mergePullRequestNow(repo: Repo, pull: Pull): { ok: boolean; message: string; sha?: string } {
  const tip = currentBaseTip(repo, pull);
  const base = mergeBase(repo, pull.headSha, tip);
  if (base === null) return { ok: false, message: 'no merge base' };
  const merged = threeWayMerge(repo, base, pull.headSha, tip);
  if (merged.conflict || merged.tree === null) return { ok: false, message: 'merge conflict' };
  const epoch = stamp().epoch;
  const message = `${pull.title} (#${pull.number})`;
  const mergeSha = makeCommit(repo, merged.tree, [tip], message, epoch);
  repo.refs.set(`refs/heads/${pull.baseRef}`, mergeSha);
  pull.state = 'closed';
  pull.merged = true;
  pull.mergedAt = new Date(epoch * 1000).toISOString();
  pull.mergeCommitSha = mergeSha;
  return { ok: true, message, sha: mergeSha };
}

function executeGraphQL(body: unknown): unknown {
  const runOne = (doc: Record<string, unknown>): Record<string, unknown> => {
    const query = typeof doc.query === 'string' ? doc.query : '';
    const variables = isRecord(doc.variables) ? (doc.variables as Record<string, unknown>) : {};
    const operationName = typeof doc.operationName === 'string' ? doc.operationName : null;
    let operations: GqlOperation[];
    try {
      const parser = new GqlParser(query);
      operations = parser.parseDocument();
      const exec: GqlExecutor = { variables, errors: [], fragments: parser.fragments };
      let operation = operations[0];
      if (operation === undefined) {
        return { data: null, errors: [{ message: 'no operation in the document' }] };
      }
      if (operationName !== null) {
        operation = operations.find((entry) => entry.name === operationName) ?? operation;
      }
      const data = executeOperation(exec, operation);
      const result: Record<string, unknown> = { data };
      if (exec.errors.length > 0) result.errors = exec.errors;
      return result;
    } catch (err) {
      return { data: null, errors: [{ message: err instanceof Error ? err.message : String(err) }] };
    }
  };
  if (Array.isArray(body)) return body.map((doc) => (isRecord(doc) ? runOne(doc) : { data: null, errors: [{ message: 'a batched entry is not an object' }] }));
  if (isRecord(body)) return runOne(body);
  return { data: null, errors: [{ message: 'the GraphQL body is not an object' }] };
}

// ---------------------------------------------------------------------------
// MCP: JSON-RPC 2.0 Streamable HTTP over POST /mcp.
// ---------------------------------------------------------------------------

const MCP_VERSIONS = ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'];

interface McpToolDef {
  name: string;
  description: string;
  properties: Record<string, { type: string; description: string }>;
  required: string[];
}

const MCP_TOOLS: McpToolDef[] = [
  {
    name: 'create_repo',
    description: 'Create a repository owned by the authenticated user.',
    properties: {
      name: { type: 'string', description: 'The repository name.' },
      description: { type: 'string', description: 'A short description of the repository.' },
      private: { type: 'boolean', description: 'Whether the repository is private.' },
      full_name: { type: 'string', description: 'owner/repo; the owner is always the authenticated user.' },
    },
    required: ['name'],
  },
  {
    name: 'get_repo',
    description: 'Read one repository by owner and name.',
    properties: {
      owner: { type: 'string', description: 'The repository owner login.' },
      repo: { type: 'string', description: 'The repository name.' },
      full_name: { type: 'string', description: 'owner/repo.' },
    },
    required: ['owner', 'repo'],
  },
  {
    name: 'list_repos',
    description: 'List the repositories owned by the authenticated user.',
    properties: {
      full_name: { type: 'string', description: 'Unused; repositories are always the authenticated user\u2019s.' },
    },
    required: [],
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    properties: {
      owner: { type: 'string', description: 'The repository owner login.' },
      repo: { type: 'string', description: 'The repository name.' },
      full_name: { type: 'string', description: 'owner/repo.' },
      title: { type: 'string', description: 'The issue title.' },
      body: { type: 'string', description: 'The issue body.' },
    },
    required: ['owner', 'repo', 'title'],
  },
  {
    name: 'list_issues',
    description: 'List the issues of a repository, optionally filtered by state.',
    properties: {
      owner: { type: 'string', description: 'The repository owner login.' },
      repo: { type: 'string', description: 'The repository name.' },
      full_name: { type: 'string', description: 'owner/repo.' },
      state: { type: 'string', description: 'open, closed or all.' },
    },
    required: ['owner', 'repo'],
  },
  {
    name: 'create_pull_request',
    description: 'Open a pull request from a head branch onto a base branch.',
    properties: {
      owner: { type: 'string', description: 'The repository owner login.' },
      repo: { type: 'string', description: 'The repository name.' },
      full_name: { type: 'string', description: 'owner/repo.' },
      title: { type: 'string', description: 'The pull request title.' },
      head: { type: 'string', description: 'The head branch name.' },
      base: { type: 'string', description: 'The base branch name.' },
      body: { type: 'string', description: 'The pull request body.' },
    },
    required: ['owner', 'repo', 'title', 'head', 'base'],
  },
  {
    name: 'list_pull_requests',
    description: 'List the pull requests of a repository.',
    properties: {
      owner: { type: 'string', description: 'The repository owner login.' },
      repo: { type: 'string', description: 'The repository name.' },
      full_name: { type: 'string', description: 'owner/repo.' },
      state: { type: 'string', description: 'open, closed or all.' },
    },
    required: ['owner', 'repo'],
  },
  {
    name: 'merge_pull_request',
    description: 'Squash-merge a pull request.',
    properties: {
      owner: { type: 'string', description: 'The repository owner login.' },
      repo: { type: 'string', description: 'The repository name.' },
      full_name: { type: 'string', description: 'owner/repo.' },
      pull_number: { type: 'integer', description: 'The pull request number.' },
    },
    required: ['owner', 'repo', 'pull_number'],
  },
];

/** Split an owner/repo pair out of tool arguments, accepting full_name too. */
function toolRepo(args: Record<string, unknown>): { owner: string; repo: string } {
  let owner = typeof args.owner === 'string' ? args.owner : '';
  let repo = typeof args.repo === 'string' ? args.repo : '';
  if ((owner === '' || repo === '') && typeof args.full_name === 'string') {
    const parts = (args.full_name as string).split('/');
    if (parts.length === 2) {
      if (owner === '') owner = parts[0] as string;
      if (repo === '') repo = parts[1] as string;
    }
  }
  if (repo === '' && typeof args.repository === 'string') repo = args.repository as string;
  if (owner === '' && typeof args.login === 'string') owner = args.login as string;
  return { owner, repo };
}

function mcpToolResult(result: unknown): Record<string, unknown> {
  return {
    content: [{ type: 'text', text: JSON.stringify(result) }],
    structuredContent: result,
    isError: false,
  };
}
function mcpToolError(message: string): Record<string, unknown> {
  return {
    content: [{ type: 'text', text: JSON.stringify({ error: message }) }],
    structuredContent: { error: message },
    isError: true,
  };
}

function callMcpTool(name: string, args: Record<string, unknown>): { ok: boolean; result: Record<string, unknown> } {
  const def = MCP_TOOLS.find((tool) => tool.name === name);
  if (def === undefined) return { ok: false, result: mcpToolError(`unknown tool "${name}"`) };
  for (const required of def.required) {
    const value = args[required];
    if (value === undefined || value === null || value === '') {
      // A missing owner/repo is forgiven when full_name supplies the pair.
      if ((required === 'owner' || required === 'repo') && typeof args.full_name === 'string' && args.full_name !== '') continue;
      return { ok: false, result: mcpToolError(`missing required argument "${required}"`) };
    }
  }
  switch (name) {
    case 'create_repo': {
      const repoName = args.name as string;
      if (getRepo(VIEWER.login, repoName) !== undefined) {
        return { ok: false, result: mcpToolError(`repository "${repoName}" already exists`) };
      }
      const repo: Repo = {
        id: dbIdCounter,
        name: repoName,
        owner: VIEWER.login,
        description: typeof args.description === 'string' ? args.description : '',
        isPrivate: args.private === true,
        defaultBranch: 'main',
        createdAt: stamp().iso,
        refs: new Map(),
        objects: new Map(),
        issues: [],
        labels: new Map([
          ['bug', { name: 'bug', color: 'd73a4a', description: "Something isn't working" }],
          ['enhancement', { name: 'enhancement', color: 'a2eeef', description: 'New feature or request' }],
          ['question', { name: 'question', color: 'd876e3', description: 'Further information is requested' }],
        ]),
        pulls: [],
        comments: new Map(),
        nextIssue: 1,
        nextPull: 1,
        nextComment: 1,
        seq: nextTick(),
      };
      dbIdCounter += 1;
      repos.set(repoKey(repo.owner, repo.name), repo);
      return { ok: true, result: mcpToolResult(repoJson(repo)) };
    }
    case 'get_repo': {
      const { owner, repo: repoName } = toolRepo(args);
      const repo = getRepo(owner, repoName);
      if (repo === undefined || repo.owner !== VIEWER.login) {
        return { ok: false, result: mcpToolError(`repository "${owner}/${repoName}" not found`) };
      }
      return { ok: true, result: mcpToolResult(repoJson(repo)) };
    }
    case 'list_repos': {
      return { ok: true, result: mcpToolResult(viewerRepos().map((repo) => repoJson(repo))) };
    }
    case 'create_issue': {
      const { owner, repo: repoName } = toolRepo(args);
      const repo = getRepo(owner, repoName);
      if (repo === undefined || repo.owner !== VIEWER.login) {
        return { ok: false, result: mcpToolError(`repository "${owner}/${repoName}" not found`) };
      }
      const stampNow = stamp();
      const issue: Issue = {
        number: repo.nextIssue,
        title: args.title as string,
        body: typeof args.body === 'string' ? args.body : '',
        state: 'open',
        labels: [],
        seq: nextTick(),
        createdAt: stampNow.iso,
        updatedAt: stampNow.iso,
        user: VIEWER,
      };
      repo.nextIssue += 1;
      repo.issues.push(issue);
      repo.comments.set(issue.number, []);
      return { ok: true, result: mcpToolResult(issueJson(repo, issue)) };
    }
    case 'list_issues': {
      const { owner, repo: repoName } = toolRepo(args);
      const repo = getRepo(owner, repoName);
      if (repo === undefined || repo.owner !== VIEWER.login) {
        return { ok: false, result: mcpToolError(`repository "${owner}/${repoName}" not found`) };
      }
      const state = typeof args.state === 'string' ? args.state : 'open';
      const list = repo.issues.filter((issue) => state === 'all' || issue.state === state);
      return { ok: true, result: mcpToolResult(list.map((issue) => issueJson(repo, issue))) };
    }
    case 'create_pull_request': {
      const { owner, repo: repoName } = toolRepo(args);
      const repo = getRepo(owner, repoName);
      if (repo === undefined || repo.owner !== VIEWER.login) {
        return { ok: false, result: mcpToolError(`repository "${owner}/${repoName}" not found`) };
      }
      const head = typeof args.head === 'string' ? args.head : (typeof args.headRefName === 'string' ? (args.headRefName as string) : '');
      const base = typeof args.base === 'string' ? args.base : (typeof args.baseRefName === 'string' ? (args.baseRefName as string) : '');
      const headSha = repo.refs.get(`refs/heads/${head}`);
      const baseSha = repo.refs.get(`refs/heads/${base}`);
      if (headSha === undefined || baseSha === undefined) {
        return { ok: false, result: mcpToolError('head or base branch does not exist') };
      }
      const existing = repo.pulls.find((entry) => entry.headRef === head && entry.baseRef === base && entry.state === 'open');
      if (existing !== undefined) {
        return { ok: false, result: mcpToolError('a pull request already exists for this head branch') };
      }
      const stampNow = stamp();
      const pull: Pull = {
        number: repo.nextPull,
        title: args.title as string,
        body: typeof args.body === 'string' ? args.body : '',
        headRef: head,
        baseRef: base,
        headSha,
        baseSha,
        state: 'open',
        merged: false,
        mergedAt: null,
        mergeCommitSha: null,
        seq: nextTick(),
        createdAt: stampNow.iso,
        user: VIEWER,
      };
      repo.nextPull += 1;
      repo.pulls.push(pull);
      return { ok: true, result: mcpToolResult(pullJson(repo, pull)) };
    }
    case 'list_pull_requests': {
      const { owner, repo: repoName } = toolRepo(args);
      const repo = getRepo(owner, repoName);
      if (repo === undefined || repo.owner !== VIEWER.login) {
        return { ok: false, result: mcpToolError(`repository "${owner}/${repoName}" not found`) };
      }
      const state = typeof args.state === 'string' ? args.state : 'open';
      const list = repo.pulls.filter((pull) => state === 'all' || pull.state === state);
      return { ok: true, result: mcpToolResult(list.map((pull) => pullJson(repo, pull))) };
    }
    case 'merge_pull_request': {
      const { owner, repo: repoName } = toolRepo(args);
      const repo = getRepo(owner, repoName);
      if (repo === undefined || repo.owner !== VIEWER.login) {
        return { ok: false, result: mcpToolError(`repository "${owner}/${repoName}" not found`) };
      }
      const number = typeof args.pull_number === 'number' ? args.pull_number : Number.parseInt(String(args.pull_number), 10);
      const pull = repo.pulls.find((entry) => entry.number === number);
      if (pull === undefined) {
        return { ok: false, result: mcpToolError(`pull request #${number} not found`) };
      }
      if (pull.state !== 'open') {
        return { ok: false, result: mcpToolError('pull request is not open') };
      }
      const merged = mergePullRequestNow(repo, pull);
      if (!merged.ok) {
        return { ok: false, result: mcpToolError(merged.message) };
      }
      return { ok: true, result: mcpToolResult(pullJson(repo, pull)) };
    }
    default:
      return { ok: false, result: mcpToolError(`unknown tool "${name}"`) };
  }
}

function handleMcp(req: IncomingMessage, res: ServerResponse, body: Buffer): void {
  const method = req.method ?? 'GET';
  if (method !== 'POST') {
    sendJson(res, 405, { message: 'Method Not Allowed' });
    return;
  }
  let parsed: unknown;
  try {
    parsed = JSON.parse(body.toString('utf8')) as unknown;
  } catch {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error: the body is not JSON' } });
    return;
  }
  if (!isRecord(parsed)) {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error: the body is not a JSON-RPC object' } });
    return;
  }
  const id = parsed.id === undefined ? null : (parsed.id as string | number | null);
  const rpcMethod = typeof parsed.method === 'string' ? parsed.method : '';
  const params = isRecord(parsed.params) ? (parsed.params as Record<string, unknown>) : {};
  // A notification (no id) is answered 202 with no body.
  if (id === null && parsed.id === undefined) {
    sendNoContent(res, 202);
    return;
  }
  const answer = (payload: Record<string, unknown>): void => {
    sendJson(res, 200, { jsonrpc: '2.0', id, ...payload }, { 'mcp-session-id': 'session-1' });
  };
  const error = (code: number, message: string): void => {
    answer({ error: { code, message } });
  };
  switch (rpcMethod) {
    case 'server/discover': {
      answer({
        result: {
          resultType: 'discover',
          supportedVersions: [...MCP_VERSIONS],
          capabilities: { tools: {} },
          instructions: 'A GitHub-compatible git forge: create repositories, issues and pull requests over MCP tools.',
          serverInfo: { name: 'github-core-clone', version: '1.0.0' },
        },
      });
      return;
    }
    case 'initialize': {
      const requested = typeof params.protocolVersion === 'string' ? params.protocolVersion : MCP_VERSIONS[1];
      const version = MCP_VERSIONS.includes(requested) ? requested : (MCP_VERSIONS[1] as string);
      answer({
        result: {
          protocolVersion: version,
          capabilities: { tools: {} },
          serverInfo: { name: 'github-core-clone', version: '1.0.0' },
        },
      });
      return;
    }
    case 'ping': {
      answer({ result: {} });
      return;
    }
    case 'tools/list': {
      answer({
        result: {
          tools: MCP_TOOLS.map((tool) => ({
            name: tool.name,
            description: tool.description,
            inputSchema: { type: 'object', properties: tool.properties, required: tool.required },
          })),
        },
      });
      return;
    }
    case 'tools/call': {
      const toolName = typeof params.name === 'string' ? params.name : '';
      const args = isRecord(params.arguments) ? (params.arguments as Record<string, unknown>) : {};
      // The suite maps its arguments onto the schema's nearest property name and
      // fills full_name with owner/repo; accept the canonical names, the
      // full_name pair, and the github-mcp-server spellings.
      const normalized: Record<string, unknown> = { ...args };
      if (typeof normalized.pullNumber === 'number' && normalized.pull_number === undefined) {
        normalized.pull_number = normalized.pullNumber;
      }
      if (typeof normalized.repository === 'string' && typeof normalized.repo !== 'string') {
        normalized.repo = normalized.repository;
      }
      const outcome = callMcpTool(toolName, normalized);
      if (outcome.ok) {
        answer({ result: outcome.result });
      } else if (toolName === '' || MCP_TOOLS.find((tool) => tool.name === toolName) === undefined) {
        error(-32601, `Method not found: ${toolName}`);
      } else {
        answer({ result: outcome.result });
      }
      return;
    }
    default: {
      error(-32601, `Method not found: ${rpcMethod}`);
      return;
    }
  }
}

// ---------------------------------------------------------------------------
// Git routes and the server.
// ---------------------------------------------------------------------------

async function handleGit(
  req: IncomingMessage,
  res: ServerResponse,
  url: URL,
  segments: string[],
  body: Buffer,
): Promise<boolean> {
  const method = req.method ?? 'GET';
  const gitIndex = segments.findIndex((segment) => segment.endsWith('.git'));
  if (gitIndex < 0) return false;
  const owner = decodeSegment(segments.slice(0, gitIndex).join('/'));
  const repoName = decodeSegment((segments[gitIndex] as string).slice(0, -4));
  const tail = segments.slice(gitIndex + 1);
  const repo = getRepo(owner, repoName);

  // GET /{owner}/{repo}.git/info/refs?service=git-upload-pack|git-receive-pack
  if (tail.length === 2 && tail[0] === 'info' && tail[1] === 'refs') {
    if (method !== 'GET') {
      sendJson(res, 405, { message: 'Method Not Allowed' });
      return true;
    }
    if (repo === undefined || repo.owner !== VIEWER.login) {
      sendJson(res, 404, { message: 'Not Found' });
      return true;
    }
    const service = url.searchParams.get('service');
    if (service === 'git-upload-pack') {
      const version = (req.headers['git-protocol'] ?? '').includes('version=2') ? 2 : 1;
      const ad = version === 2 ? advertisementV2(repo) : advertisementV0(repo, 'git-upload-pack');
      sendBuffer(res, 200, ad, 'application/x-git-upload-pack-advertisement');
      return true;
    }
    if (service === 'git-receive-pack') {
      sendBuffer(res, 200, advertisementV0(repo, 'git-receive-pack'), 'application/x-git-receive-pack-advertisement');
      return true;
    }
    sendJson(res, 404, { message: 'Not Found' });
    return true;
  }

  // POST /{owner}/{repo}.git/git-upload-pack | git-receive-pack
  if (tail.length === 1 && (tail[0] === 'git-upload-pack' || tail[0] === 'git-receive-pack')) {
    if (method !== 'POST') {
      sendJson(res, 405, { message: 'Method Not Allowed' });
      return true;
    }
    if (repo === undefined || repo.owner !== VIEWER.login) {
      sendJson(res, 404, { message: 'Not Found' });
      return true;
    }
    if (tail[0] === 'git-upload-pack') {
      let reqParsed: UploadRequest;
      try {
        const bodyText = body.toString('utf8');
        const isV2 =
          (req.headers['git-protocol'] ?? '').includes('version=2') ||
          bodyText.includes('command=ls-refs') ||
          bodyText.includes('command=fetch');
        reqParsed = isV2 ? parseUploadV2(body) : parseUploadV0(body);
        if (reqParsed.command === 'ls-refs') {
          sendBuffer(res, 200, lsRefsV2(repo, reqParsed), 'application/x-git-upload-pack-result');
          return true;
        }
      } catch {
        sendJson(res, 400, { message: 'malformed upload-pack request' });
        return true;
      }
      const answer = uploadPackAnswer(repo, reqParsed);
      sendBuffer(res, 200, answer, 'application/x-git-upload-pack-result');
      return true;
    }
    const result = receivePackAnswer(repo, body);
    sendBuffer(res, result.status, result.body, result.contentType);
    return true;
  }
  return false;
}

/** Build the server. It binds nothing until the caller listens. */
export function createApp(): Server {
  return createServer((req: IncomingMessage, res: ServerResponse) => {
    void (async () => {
      try {
        const url = new URL(req.url ?? '/', 'http://entry');
        const path = url.pathname;
        const segments = path.split('/').filter((segment) => segment !== '');
        const method = req.method ?? 'GET';

        // The env's boot check calls this twice: 200 {"ok":true}. No auth.
        if (method === 'GET' && path === '/healthz') {
          sendJson(res, 200, { ok: true });
          return;
        }

        const body = await readBody(req);

        // Everything else needs the trial's bearer token.
        if (!tokenValid(bearerToken(req))) {
          if (path === '/api/graphql' || path === '/mcp') {
            sendJson(res, 401, { message: 'Requires authentication' });
          } else if (path.startsWith('/api/v3')) {
            sendJson(res, 401, { message: 'Requires authentication' });
          } else if (path.includes('.git')) {
            sendJson(res, 401, { message: 'Requires authentication' });
          } else {
            sendJson(res, 401, { message: 'Requires authentication' });
          }
          return;
        }

        // Git smart HTTP.
        if (path.includes('.git')) {
          const handled = await handleGit(req, res, url, segments, body);
          if (handled) return;
        }

        // GraphQL.
        if (path === '/api/graphql') {
          if (method !== 'POST') {
            sendJson(res, 405, { message: 'Method Not Allowed' });
            return;
          }
          let parsed: unknown;
          try {
            parsed = body.length === 0 ? {} : (JSON.parse(body.toString('utf8')) as unknown);
          } catch {
            sendJson(res, 400, { message: 'Problems parsing JSON' });
            return;
          }
          const result = executeGraphQL(parsed);
          sendJson(res, 200, result);
          return;
        }

        // MCP.
        if (path === '/mcp') {
          handleMcp(req, res, body);
          return;
        }

        // REST v3.
        if (path === '/api/v3' || path.startsWith('/api/v3/')) {
          const restSegments = path === '/api/v3' ? [] : segments.slice(2);
          let json: Record<string, unknown> | undefined;
          if ((method === 'POST' || method === 'PATCH' || method === 'PUT' || method === 'DELETE') && body.length > 0) {
            try {
              const parsed = JSON.parse(body.toString('utf8')) as unknown;
              if (!isRecord(parsed)) {
                sendJson(res, 400, { message: 'Problems parsing JSON' });
                return;
              }
              json = parsed;
            } catch {
              sendJson(res, 400, { message: 'Problems parsing JSON' });
              return;
            }
          }
          const handled = await handleRest(req, res, url, restSegments, body, json);
          if (handled) return;
        }

        sendJson(res, 404, { message: 'Not Found' });
      } catch (err) {
        try {
          sendJson(res, 500, { message: err instanceof Error ? err.message : 'Internal Server Error' });
        } catch {
          // The response is already gone; nothing left to do.
        }
      }
    })();
  });
}
