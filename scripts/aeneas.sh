#!/usr/bin/env bash
# Check out the Aeneas Lean library with `aeneas.patch` applied: `Result` gets a `random` effect.
# Only the patch is tracked. The checkout is in `./aeneas` (ignored), and `lakefile.toml` requires
# it by path. The extraction binaries stay the pinned release ones (`setup-tools.sh`): the patch
# changes the meaning of `Result`, not the text that Aeneas generates for the examples.
#
#   bash scripts/aeneas.sh              clone Aeneas at the pinned commit and apply the patch
#   bash scripts/aeneas.sh check        check that `./aeneas` is the pinned commit with the patch
#   bash scripts/aeneas.sh save-patch   write the changes in `./aeneas` to `aeneas.patch`
#
# The patch is from https://github.com/Beneficial-AI-Foundation/toy-bridge.
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/env.sh"

AENEAS_REPO="${AENEAS_REPO:-https://github.com/AeneasVerif/aeneas.git}"
# Upstream commit that the patch applies to. It is also the commit of the extraction binaries.
AENEAS_REV=da2b22e78d8fd5f076a902a5617c34038409fb79
PATCH="$BRIDGE_ROOT/aeneas.patch"
DIR="$BRIDGE_ROOT/aeneas"

check_rev() {
  local actual
  actual="$(git -C "$DIR" rev-parse HEAD)"
  if [[ "$actual" != "$AENEAS_REV" ]]; then
    echo "Error: $DIR is at $actual, expected the pinned commit $AENEAS_REV." >&2
    exit 1
  fi
}

# The tree of the pinned commit with the patch applied, and the tree of the checkout with its
# changes, untracked files included. Both use a temporary index, so the checkout is not changed.
tree() {
  local index result
  index="$(mktemp)"
  rm -f "$index"
  if [[ "$1" == patched ]]; then
    GIT_INDEX_FILE="$index" git -C "$DIR" read-tree "$AENEAS_REV"
    GIT_INDEX_FILE="$index" git -C "$DIR" apply --cached "$PATCH"
  else
    GIT_INDEX_FILE="$index" git -C "$DIR" read-tree HEAD
    GIT_INDEX_FILE="$index" git -C "$DIR" add -A
  fi
  result="$(GIT_INDEX_FILE="$index" git -C "$DIR" write-tree)"
  rm -f "$index"
  echo "$result"
}

check() {
  check_rev
  if [[ "$(tree patched)" != "$(tree checkout)" ]]; then
    echo "Error: $DIR is not the pinned commit with exactly $PATCH applied." >&2
    echo "Run 'bash $0 save-patch' to update the patch, or remove $DIR and run 'bash $0'." >&2
    exit 1
  fi
}

checkout() {
  if [[ ! -e "$DIR" ]]; then
    git clone -q "$AENEAS_REPO" "$DIR"
    git -C "$DIR" checkout -q -b random-effect "$AENEAS_REV"
  fi
  check_rev
  if [[ -z "$(git -C "$DIR" status --porcelain)" ]]; then
    git -C "$DIR" apply "$PATCH"
    echo "Applied $PATCH"
  else
    check
    echo "Patch already applied"
  fi
}

save_patch() {
  check_rev
  # Record new files as intent-to-add, so that `git diff` includes them.
  git -C "$DIR" add -N .
  git -C "$DIR" diff --binary "$AENEAS_REV" > "$PATCH"
  echo "Wrote $PATCH"
}

case "${1:-checkout}" in
  checkout) checkout ;;
  check) check ;;
  save-patch) save_patch ;;
  *)
    echo "Usage: bash $0 [checkout|check|save-patch]" >&2
    exit 1
    ;;
esac
