# VERIFICATION — openai/math "ETH is False" Lean proof (SubexponentialSAT)

Run date: 2026-10-27 23:45 → 2026-10-28 02:25 (+03). Every command, exit status, wall time and peak RSS: `COMMANDS.log` (host) and `logs/vm/COMMANDS-vm.log` (Linux VM). All logs are in `logs/`.

## 1. Machine and versions

| Item | Value |
|---|---|
| Host | macOS 26.5.1 (25F80), Darwin 25.5.0 arm64 |
| Chip / cores | Apple M5 Max, 18 cores (6 performance + 12 efficiency) |
| RAM | 128 GiB (137438953472 B) |
| Free disk at start | 173 GiB |
| elan | 4.2.4 (227caca13 2026-08-25), user-local in `~/.elan`, installed with `--no-modify-path` (shell profiles not modified); installer SHA-256 `a620ff1641616222c8d37c54845492004bb84d6877cdbc944dd65c1aa685bf53` |
| Lean (host) | `Lean (version 4.34.1, arm64-apple-darwin24.6.0, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)` |
| git | 2.50.1 (Apple Git-155) |
| Linux VM (Phase 5 only) | Lima 2.1.3, vz, Ubuntu 26.04 LTS, kernel `7.0.0-15-generic` aarch64, 16 vCPU, 80 GiB, LSMs `lockdown,capability,landlock,yama,apparmor,ima,evm`; state in `~/eth-verify/lima` |
| Lean (VM) | `Lean (version 4.34.1, aarch64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)` |
| Comparator tools (VM) | comparator `d03acab154d269c06e60e4de7e4cc85deebff94b` (tag v4.34.0); lean4export `076e8e57707e813375e8f9da8bf989799ace9680` (tag v4.34.0, exactly the revision comparator v4.34.0 pins), built with toolchain v4.34.1 so it reads 4.34.1 .olean files; landrun 0.1.18 from `main` @ `ec104f6edc1e14d7fec6d31146f1ec6f9c192c5a`, built with go1.27.3 (tarball SHA-256 checked against go.dev) |

## 2. Commit and hashes

`git rev-parse HEAD` → `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a` (host clone `logs/rev-parse.txt`; VM fresh fetch `logs/vm/vm-math-rev.txt`, same).
`lean/lean-toolchain` → `leanprover/lean4:v4.34.1`. Mathlib checkout → `d13f23b723b8a846827a245b89c10fc7d3f11612` (host and VM).

| File | SHA-256 (host = VM) | Expected | Match |
|---|---|---|---|
| lean/ComparatorChallenges/SubexponentialSAT.lean | 4183b2057cff350d66848215ff7167196dfc20e1891b598fdddea59077a76685 | same | ✅ |
| lean/ComparatorChallenges/SubexponentialSAT.json | debbfdc9c01104d2369be80da5180978275106df8b685f693fba7ce7da7c5b19 | same | ✅ |
| lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean | 040360a8465957622d934e5f1bb4f2cce8dab950e78f52033fbf70da493184f5 | same | ✅ |

`git status --porcelain` of the repo stayed empty after all builds (host and VM). No file under the cloned repository was modified. The 23 lines `warning: <pkg>: repository '.lake/packages/<pkg>' has local changes` in every lake invocation come from the lakefile's compatibility patches (`lean/patches/*-lean4341.patch`), which it applies to dependency checkouts under `.lake/packages`. They are not repo files.

## 3. Mathlib cache

- `lake update` (exit 0, 841.3 s): resolved 42 packages; Mathlib's post-update hook ran the cache: `Attempting to download 8908 file(s) … https://cache.mathlib.org/mathlib4-master` → `Downloaded: 8908 file(s) [attempted 8908/8908 = 100%]`, `Decompressed 8908 file(s)` (`logs/lake-update.log`).
- `lake exe cache get` (exit 0, 11.9 s): `No files to download` / `Already decompressed 8908 file(s)` (`logs/cache-get.log`).
- `lake build Mathlib` (exit 0, 5.2 s): `Build completed successfully (8923 jobs).`: cache hit, 0 modules compiled. Mathlib was not built from source.
- VM (fresh): `lake update` exit 0 (766.7 s) with the same 8908/8908 download and decompress; `lake exe cache get` exit 0 `No files to download`.

## 4. Per-target builds (host, macOS, default job count)

Peak RSS = `/usr/bin/time -l` max RSS, the largest single process among reaped descendants. Aggregate RSS of all lean/lake processes, sampled every 15 s, peaked at **75.22 GiB** during the Final build (`logs/mem-samples.tsv`).

| Target | Exit | Wall time | Peak RSS | Lean modules compiled | Warnings | Errors |
|---|---|---|---|---|---|---|
| `Mathlib` (sanity) | 0 | 5.2 s | 1.68 GiB | 0 (8923 jobs, all cached) | 0 | 0 |
| `ComparatorChallenges.SubexponentialSAT` | 0 | 27.8 s | 5.57 GiB | 1 (8924 jobs) | 1: `warning: ComparatorChallenges/SubexponentialSAT.lean:194:8: declaration uses `sorry`` (by design: line 194 is the theorem name `exact_count_and_sat`, and the file's only `sorry` token is at line 218) | 0 |
| `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Final` | 0 | 2079.6 s (34.7 min) | 15.67 GiB | 2569 (11492 jobs) | 0 | 0 |
| `OAI.Algorithms.SubexponentialSAT.Main` | 0 | 413.9 s (6.9 min) | 7.12 GiB | 522 (+8 replayed; 12014 jobs) | 0 | 0 |

Apart from the single by-design `sorry` warning above, every `warning:` line in these logs is one of the 23 lake "local changes" lines described in §2. No `-j2` retry was needed. The builds also print 19 informational `#print axioms` results from `#print axioms` commands in the sources. Every one lists only `[propext, Classical.choice, Quot.sound]` (union over the build-Final, build-Main and comparator logs: exactly those three).

Supporting, non-kernel evidence (`logs/source-grep.txt`): grepping the 3,977 `.lean` files under `OAI/Algorithms/SubexponentialSAT` for `axiom`, `sorry`, `admit`, `native_decide`, `ofReduceBool`, `implemented_by` and `@[extern` finds only 6 doc-comment uses of the English word "admit".

## 5. `#print axioms` (verbatim)

Command: `lake env lean OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean` (exit 0, 7.6 s), run after the Final build succeeded. The 23 lake "local changes" lines are omitted here. Full output: `logs/axioms-Final-file.log`.

```
'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.compiled_exact_count_and_sat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_eth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sat_polynomial_space' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.original_sat_main' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Cross-checks, all exit 0, same result: `logs/axioms-scratch.log` (`~/eth-verify/scratch/PrintAxioms.lean`, which imports `…SqrtLogSpace.Final`) and `logs/axioms-scratch-Main.log` (`scratch/PrintAxiomsMain.lean`, which imports `OAI.Algorithms.SubexponentialSAT.Main`):

```
'OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

**PASS**: each of `exact_count_and_sat`, `exact_count_eth`, `sat_polynomial_space` and `original_sat_main` (and `compiled_exact_count_and_sat`) depends on exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no `Lean.ofReduceBool`, no custom axioms.

## 6. Comparator (verbatim)

**Why it ran in a VM:** `landrun` relies on Linux Landlock. It cannot be installed or run on macOS, and comparator v4.34.0 runs both `lake build` and `lean4export` inside landrun. The existing OrbStack VM has only 16 GiB, below the 15.67 GiB single-process peak seen above. So a dedicated Lima VM was created with all state under `~/eth-verify/lima`; OrbStack's configuration was not touched. In the VM, `openai/math` was freshly fetched at the pinned commit with the same hashes, and `lake update` and `lake exe cache get` were run. The project (Challenge or Solution) was **never built outside Comparator** (`.lake/build` did not exist before the run). Lean 4.35's built-in `lake comparator` does not exist in v4.34.1, so the standalone comparator at tag v4.34.0 was used.

Command, from `~/math/lean` in the VM, following the README's `systemd-run` guard. One deviation: there is no TTY, so `--wait --collect --pipe` was used instead of `--pty`; the `RestrictAddressFamilies=~AF_UNIX` property is unchanged:

```
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --wait --collect --pipe -E PATH="$PATH" -E HOME="$HOME" --working-directory "$(pwd)" -- bash -c 'ulimit -n 10240; lake env comparator ComparatorChallenges/SubexponentialSAT.json'
```

Exit 0, wall 2021.3 s, systemd-reported memory peak 49G. The output below is verbatim, except that 69 lake "local changes" lines, 3091 `✔/ℹ [n/12014] Built …` progress lines and 19 `info: … depends on axioms` messages (with their continuation lines) are removed. All of those info messages list only the three standard axioms. Full 3,234-line output: `logs/vm/comparator.log`.

```
Running as unit: run-p28672-i9778.service; invocation ID: 0f58ddfa7642472e8433f218b4224609
Building ComparatorChallenges.SubexponentialSAT
⚠ [8924/8924] Built ComparatorChallenges.SubexponentialSAT (2.3s)
warning: ComparatorChallenges/SubexponentialSAT.lean:194:8: declaration uses `sorry`
Build completed successfully (8924 jobs).
Exporting #[Quot, Quot.mk, Quot.lift, Quot.ind, OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat, propext, Quot.sound, Classical.choice, Nat.add, Nat.sub, Nat.mul, Nat.pow, Nat.gcd, Nat.div, Nat.mod, Nat.beq, Nat.ble, Nat.land, Nat.lor, Nat.xor, Nat.shiftLeft, Nat.shiftRight, String.ofList, Char.ofNat, List, eagerReduce, Nat, String, String.mk, Char, optParam, autoParam, semiOutParam, outParam] from ComparatorChallenges.SubexponentialSAT
Building OAI.Algorithms.SubexponentialSAT.Main
Build completed successfully (12014 jobs).
Exporting #[Quot, Quot.mk, Quot.lift, Quot.ind, OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat, propext, Quot.sound, Classical.choice, Nat.add, Nat.sub, Nat.mul, Nat.pow, Nat.gcd, Nat.div, Nat.mod, Nat.beq, Nat.ble, Nat.land, Nat.lor, Nat.xor, Nat.shiftLeft, Nat.shiftRight, String.ofList, Char.ofNat, List, eagerReduce, Nat, String, String.mk, Char, optParam, autoParam, semiOutParam, outParam] from OAI.Algorithms.SubexponentialSAT.Main
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
          Finished with result: success
Main processes terminated with: code=exited, status=0/SUCCESS
               Service runtime: 33min 43.962s
             CPU time consumed: 4h 53min 41.770s
                   Memory peak: 49G (swap: 0B)
```

Landlock sanity test in the same VM (`logs/vm/landrun-sanity.log`): under landrun, a write outside the allowed path is denied (`touch: cannot touch '/tmp/lr-forbidden': Permission denied`, rc=1), and a write inside the allowed path succeeds (rc=0). The sandbox enforces on this kernel.

**PASS**: Comparator built the trusted challenge and the solution in the sandbox and exported both. It ran the Lean kernel on the solution: `Lean default kernel accepts the solution`, `Your solution is okay!`. Per the Comparator README, this success means `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat` in `OAI.Algorithms.SubexponentialSAT.Main` proves the same statement as in `ComparatorChallenges.SubexponentialSAT`, uses no axioms beyond `propext, Quot.sound, Classical.choice`, and is accepted by the Lean kernel. `enable_nanoda` is `false` in the challenge JSON, so only the built-in kernel was used.

### Phase 6: optional cross-check (separate; anthropics/formal-math)

`~/eth-verify/phase6/formal-math` @ `16a5ce41304fcdaea4e0be7c132e1c361dc26da5` (`logs/p6-rev.txt`), `eth/`, toolchain `leanprover/lean4:v4.33.1`.
- `lake exe cache get`: exit 0, 681.9 s, 8690 files downloaded and decompressed (`logs/p6-cache-get.log`).
- `lake build`: exit 0, 243.6 s, peak RSS 5.74 GiB, `Build completed successfully (9768 jobs)`. Warnings, by design: `Challenge.lean:12:8: declaration uses `sorry`` and `Challenge.lean:16:8: declaration uses `sorry``. 0 errors (`logs/p6-build.log`).
- `lake env lean scripts/PrintAxioms.lean`: exit 0 (`logs/p6-axioms.log`), verbatim:

```
'MainResults.ethIsFalse' depends on axioms: [propext, Classical.choice, Quot.sound]
'MainResults.mainTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Both theorems depend only on the three standard axioms, as expected. The Comparator was not run on formal-math; this is the `#print axioms` cross-check only.

## 7. Verdict

**KERNEL-VERIFIED.** At commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`, with all three file hashes matching, target 3.2 `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Final` built with exit 0, 0 errors and 0 Lean warnings (2569 modules). Target 3.3 `…Main` and the statement file also built; the statement file's only warning is the by-design `sorry`. Phase 4 `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for `exact_count_and_sat`, `exact_count_eth`, `sat_polynomial_space` and `original_sat_main`. Phase 5 Comparator returned exit 0 with `Lean default kernel accepts the solution` / `Your solution is okay!`. **Most important thing that did not work as specified:** Comparator cannot run on macOS, because `landrun` is Linux/Landlock-only. Phase 5 was therefore run in a dedicated Lima Ubuntu 26.04 VM (kernel 7.0) on this Mac, not natively. It was also run under `systemd-run --pipe` instead of the README's `--pty`, and the optional nanoda kernel was not enabled (the challenge JSON sets `enable_nanoda: false`).

## Notes and deviations

- Lima's image download cache was written to `~/Library/Caches/lima` (≈600 MB Ubuntu cloud image), outside `~/eth-verify`. All VM state is in `~/eth-verify/lima`. To remove the VM: `LIMA_HOME=~/eth-verify/lima limactl delete cmp`. The VM is currently stopped.
- Peak RSS values are max single-process RSS (`/usr/bin/time -l` on host; `getrusage(RUSAGE_CHILDREN)` in the VM). For the Comparator run this measures only the systemd-run client (0.01 GiB). The relevant figure is systemd's `Memory peak: 49G` for the unit.
- VM memory: total used memory sampled every 15 s peaked at 25.7 GiB (`logs/vm/vm-mem.log`); systemd's 49G unit peak also counts page cache. No OOM kills (`journalctl -k`: 0 matches).

## Log index

Host: `COMMANDS.log`, `logs/env.txt`, `logs/elan-install.log`, `logs/clone.log`, `logs/checkout.log`, `logs/rev-parse.txt`, `logs/hashes.txt`, `logs/lake-update.log`, `logs/lean-version.txt`, `logs/mathlib-rev.txt`, `logs/cache-get.log`, `logs/build-Mathlib.log`, `logs/build-Challenge.log`, `logs/build-Final.log`, `logs/build-Main.log`, `logs/phase23.status`, `logs/mem-samples.tsv`, `logs/axioms-Final-file.log`, `logs/axioms-scratch.log`, `logs/axioms-scratch-Main.log`, `logs/source-grep.txt`, `logs/lima-create.log`, `logs/lima-start.log`, `logs/lima-stop.log`, `logs/p6-*.log`.
VM (copied to `logs/vm/`): `COMMANDS-vm.log`, `vm-env.txt`, `provision.status`, `vm-math-rev.txt`, `vm-hashes.txt`, `vm-mathlib-rev.txt`, `vm-lean-version.txt`, `vm-git-status.txt`, `vm-lake-update.log`, `vm-cache-get.log`, `vm-lean4export-build.log`, `vm-comparator-build.log`, `vm-landrun-build.log`, `landrun-rev.txt`, `go.sha256check`, `comparator.log`, `comparator-filtered.log`, `landrun-sanity.log`, `vm-mem.log`.
Scripts: `bin/logrun`, `bin/env.sh`, `bin/phase23.sh`, `bin/memsampler.sh`, `bin/phase6.sh`, `vm/provision.sh`, `vm/run-comparator.sh`, `vm/logrun.py`, `scratch/PrintAxioms.lean`, `scratch/PrintAxiomsMain.lean`.
