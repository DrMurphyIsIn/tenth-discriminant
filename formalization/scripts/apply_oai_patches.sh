#!/usr/bin/env bash
# Fetch this project's Lake dependencies at the revisions pinned in lake-manifest.json and apply
# openai/math's Lean-v4.34.1 compatibility patches. Run it once, from the directory that holds
# lakefile.lean, before the first `lake build`:
#
#     scripts/apply_oai_patches.sh          # clone (if needed), patch, verify
#     scripts/apply_oai_patches.sh --check  # verify only, change nothing
#
# Why this script exists. openai/math (our only direct dependency) pins 42 packages and carries
# patches for 23 of them in lean/patches/<package>-lean4341.patch: Lean-v4.34.1 ports of
# repositories that were written for older toolchains. The patches touch Lean sources and also the
# packages' lakefile.toml / lake-manifest.json / lean-toolchain, so they must be in place before
# Lake compiles anything. openai/math's own lakefile applies them, but only to the checkout that
# openai/math itself owns as the root project (`.lake/packages` under lean/); when openai/math is a
# dependency, as it is here, Lake puts the shared packages under THIS project's .lake/packages, and
# openai/math's `post_update` hook refuses that layout ("Lake resolved an unexpected checkout").
# This script does the same work for the dependency layout, by hand and verifiably:
#
#   1. for every git package in lake-manifest.json: clone it into .lake/packages/<name> if that
#      directory does not exist, and check out the pinned revision (detached HEAD);
#   2. for every patch .lake/packages/OAI/lean/patches/<pkg>-lean4341.patch: apply it to
#      .lake/packages/<pkg> with `git apply`, unless `git apply --check --reverse` says it is
#      already applied;
#   3. verify every package: HEAD is the pinned revision; for the 23 patched packages the reverse
#      check passes (tracked tree == HEAD + patch) and every untracked file is one the patch
#      creates; print the md5 of `git diff HEAD` so the result can be compared with a reference;
#   4. openai/math's lakefile also has a configuration-time hook that looks for 11 of its
#      dependencies under its own lean/.lake/packages and would clone and patch them there (a
#      second copy, needing network access at `lake build` time). We point those 11 paths at the
#      workspace copies with relative symlinks, after checking that the remote URL recorded in the
#      clone is the one the hook expects; the hook then verifies the patched workspace copies
#      instead of cloning.
#
# `lake build` afterwards prints "repository '...' has local changes" for the 23 patched packages;
# that warning is expected and is exactly the patched state. Do not run `lake update`: it would
# re-resolve the dependencies and run openai/math's post-update hook, which fails in this layout.
#
# Requirements: bash, git, python3 (to read lake-manifest.json), md5 or md5sum. No network is needed
# for --check or when all packages are already cloned. Paths are relative to the project root.
set -euo pipefail

CHECK_ONLY=0
if [ "${1:-}" = "--check" ]; then CHECK_ONLY=1; fi

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
PKGS=.lake/packages
OAI_DIR=$PKGS/OAI/lean
# absolute, because `git -C <dir> apply <patch>` resolves a relative patch path against <dir>
PATCHES=$ROOT/$OAI_DIR/patches

if command -v md5 >/dev/null 2>&1; then md5q() { md5 -q "$@"; }; else md5q() { md5sum "$@" | cut -d' ' -f1; }; fi
md5stdin() { if command -v md5 >/dev/null 2>&1; then md5 -q; else md5sum | cut -d' ' -f1; fi; }

fail=0
note() { printf '%s\n' "$*"; }
bad() { printf 'FAIL: %s\n' "$*"; fail=1; }

# --- 1. clone / check out every git package of the manifest --------------------------------------
# name<TAB>url<TAB>rev per line
MANIFEST_ROWS=$(python3 - <<'EOF'
import json
m = json.load(open("lake-manifest.json"))
for p in m["packages"]:
    if p["type"] == "git":
        # Lake stores names like «doc-gen4» with guillemets; the checkout directory has none.
        print(p["name"].strip("\u00ab\u00bb"), p["url"], p["rev"], sep="\t")
EOF
)
mkdir -p "$PKGS"
n_pkgs=0
while IFS=$'\t' read -r name url rev; do
  [ -n "$name" ] || continue
  n_pkgs=$((n_pkgs + 1))
  dir=$PKGS/$name
  if [ ! -d "$dir/.git" ]; then
    if [ $CHECK_ONLY = 1 ]; then bad "$name: not cloned at $dir"; continue; fi
    note "cloning $name from $url"
    rm -rf "$dir"
    git clone --quiet --no-checkout "$url" "$dir"
    git -C "$dir" checkout --quiet --detach "$rev"
  fi
  head=$(git -C "$dir" rev-parse HEAD)
  if [ "$head" != "$rev" ]; then
    if [ $CHECK_ONLY = 1 ]; then bad "$name: HEAD $head, manifest pins $rev"; continue; fi
    note "$name: checking out $rev (was $head)"
    git -C "$dir" fetch --quiet origin "$rev" || git -C "$dir" fetch --quiet origin
    git -C "$dir" checkout --quiet --detach "$rev"
  fi
done <<< "$MANIFEST_ROWS"
note "manifest packages: $n_pkgs (all at their pinned revisions)"

[ -d "$PATCHES" ] || { bad "patch directory $PATCHES not found"; exit 1; }

# --- 2./3. apply and verify the patches -----------------------------------------------------------
n_patches=0
for pf in "$PATCHES"/*-lean4341.patch; do
  n_patches=$((n_patches + 1))
  pkg=$(basename "$pf" -lean4341.patch)
  dir=$PKGS/$pkg
  if [ ! -d "$dir/.git" ]; then bad "$pkg: has a patch but no checkout at $dir"; continue; fi
  if git -C "$dir" apply --check --reverse "$pf" 2>/dev/null; then
    state="already applied"
  elif git -C "$dir" apply --check "$pf" 2>/dev/null; then
    if [ $CHECK_ONLY = 1 ]; then bad "$pkg: patch not applied"; continue; fi
    git -C "$dir" apply "$pf"
    git -C "$dir" apply --check --reverse "$pf" || { bad "$pkg: patch applied but reverse check fails"; continue; }
    state="applied now"
  else
    bad "$pkg: patch neither applied nor applicable (local changes?)"; continue
  fi
  # every untracked file must be created by the patch (a `+++ b/<path>` line)
  extra=0
  while IFS= read -r u; do
    [ -n "$u" ] || continue
    if ! grep -q "^+++ b/$u\$" "$pf"; then bad "$pkg: untracked file not created by the patch: $u"; extra=1; fi
  done < <(git -C "$dir" ls-files --others --exclude-standard)
  dm=$(git -C "$dir" diff HEAD | md5stdin)
  note "[$pkg] HEAD $(git -C "$dir" rev-parse HEAD)  patch $(md5q "$pf")  git-diff-HEAD md5 $dm  $state  reverse-check OK  untracked-ok=$((1 - extra))"
done
note "patches: $n_patches"
[ "$n_patches" = 23 ] || bad "expected 23 patches, found $n_patches"

# --- 4. let openai/math's configuration-time hook find the pre-resolution packages ---------------
# The names are those in `preResolutionPatchNames` of openai/math's lean/lakefile.lean.
HOOK_PKGS="iut tate-curves-theta genl heights pi1 orbicurve-cores oka tempered-fundamental-groups elliptic-curves formal-schemes belyi"
NESTED=$OAI_DIR/.lake/packages
mkdir -p "$NESTED"
for pkg in $HOOK_PKGS; do
  dir=$PKGS/$pkg
  link=$NESTED/$pkg
  # the URL the hook expects is the one in openai/math's lakefile; the clone's origin must match it
  want=$(grep -A1 -e "require «${pkg}» from git" -e "require ${pkg} from git" "$OAI_DIR/lakefile.lean" | grep -o '"https://[^"]*"' | head -1 | tr -d '"')
  have=$(git -C "$dir" remote get-url origin)
  if [ "$want" != "$have" ]; then
    note "[$pkg] origin $have differs from the hook's URL $want: not linking (the hook will clone its own copy)"
    continue
  fi
  if [ -L "$link" ]; then
    note "[$pkg] hook link exists -> $(readlink "$link")"
  elif [ -e "$link" ]; then
    note "[$pkg] $link exists and is not a symlink; left alone"
  elif [ $CHECK_ONLY = 1 ]; then
    bad "[$pkg] hook link $link missing"
  else
    ln -s "../../../../$pkg" "$link"
    note "[$pkg] hook link created: $link -> ../../../../$pkg"
  fi
done

if [ $fail = 0 ]; then note "OK: all packages at their pinned revisions, all 23 patches applied and verified."; else note "FAILED: see the FAIL lines above."; exit 1; fi
