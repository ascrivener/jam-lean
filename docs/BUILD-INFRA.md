# Build infrastructure

A cold `lake build` takes about 4.5–5 h, both in CI and in a fresh cloud session. This note covers how
CI resumes a build that runs out of time, how a session starts from main's latest build, and what is
still open.

## CI: attempts that resume

- `ci.yml` calls the whole job, which lives in `build.yml` (a reusable workflow), up to three times:
  `attempt-1`, then `attempt-2` and `attempt-3`, each only if the attempt before it ran out of time.
- `scripts/ci-bounded.sh` runs each build command (the largest proofs, then `lake build`). Every build
  step must stop by `CI_DEADLINE`, 300 min after the job starts. The job limit is 355 min, which
  leaves time for the checks (about 30 min) or for saving `.lake`.
- If the deadline cuts off a build command, `ci-bounded.sh` sets `CI_TIMED_OUT=true` and exits 0. The
  attempt then:
  - skips the checks;
  - saves `.lake` under `lake-<os>-<hash>-<sha>-<run_id>-<run_attempt>-<attempt>`;
  - ends green with the output `timed_out=true`.
- The next attempt restores the newest cache for the same commit first (prefix `…-<sha>-`), then
  any cache for this toolchain.
- Only `attempt-3` running out of time fails the run. A re-run of the workflow then resumes from the
  saved cache.
- A real failure keeps its exit code and fails the attempt: a proof error, or an OOM kill (exit 137
  before the deadline).
- Runs on `main` are never cancelled (`concurrency` in `ci.yml`). Main always saves `.lake`. A PR
  saves only when its build did not finish, so that finished PR builds don't evict main's caches
  from the 10 GB repository cache.

## Cloud sessions: start from main's latest build

Cloud sessions can't reach the Actions cache or artifacts: the proxy refuses `/actions/` API paths,
and artifact downloads need a token. They can reach GitHub release assets of this public repository
without a token. So:

- **`scripts/publish-lake.sh`** runs at the end of every green main run (the job has
  `permissions: contents: write`). It:
  - packs `.lake` as tar + zstd, about 2.8 GB;
  - splits the archive into parts under GitHub's 2 GiB asset limit;
  - uploads the parts to the rolling prerelease `lake-cache`;
  - then points `meta.txt` at them. `meta.txt` holds `sha`, `time`, `toolchain` and `parts`, and
    only moves forward in commit time, since main's runs can overlap.

  The release keeps the previous build's parts, so a download in progress stays consistent, and
  deletes older ones. At most about 6 GB is stored. Release storage is free for a public repository.
- **`scripts/fetch-lake.sh [--force]`** installs the pinned toolchain under `~/.lean` (from the Lean
  GitHub release; no elan needed) and unpacks the published `.lake`. It uses Python's `zstandard`
  if the `zstd` binary is missing. Then `lake build` rebuilds only what differs from that commit.
  - The session proxy can reset a long download, so each part is downloaded to a file with
    `curl -C -` (resume), checked against the release's asset size, unpacked, then deleted.
  - Measured on a fresh clone at fef9243 (15 Nov 2026): 2 min 17 s for 2.76 GB, including one
    reset; the unpacked `.lake` is 11 GB. `lake build --no-build` then reports all 2670 jobs
    up to date, so the traces carry no runner paths.

## Profiling

From the import graph (1340 modules, 138 MB of source):

- `Services.Bootstrap.Code` is 8.3 MB, and 1008 modules depend on it transitively. Regenerating it
  rebuilds most of the project.
- `CodeA` has 278 transitive dependents, `CodeF` 218, `CodeX` 215 and `Services.Witness.Code` 147.
- The `PVM.*` base modules have about 1300 dependents each, which is expected.

Per-module build times from a full cold build (1305 modules, 18.1 h serial) are on branch
`claude/profiling-data`; the analysis is in `docs/profiling/` (#203). The longest import chain takes about 2 h even with unlimited cores.

## Handoff

- Done: the continuation job and the `lake-cache` publish/fetch scripts (PR #193). The first
  publish came from main at fef9243 and a fresh checkout restores it without rebuilding. A
  start-of-session line in `CLAUDE.md` points sessions to `fetch-lake.sh`.
- Done: per-module build times on branch `claude/profiling-data` (`docs/profiling/`), analysed in
  the build-time profiling proposal (#203).
