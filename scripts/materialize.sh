#!/bin/bash
# Reproduce the verification: check out the Arda repository at the tag recorded in provenance/ARDA_SOURCE,
# build the dbn island (56 modules, Lean v4.34.0-rc1, Mathlib de5ce8a9), run the axiom guard, and build the
# registry judge bundle whose challenge module has the registered statement as its TYPE.
#
#   scripts/materialize.sh                  # clone Arda at the tag into work/arda (network, ~15 min cold with cache)
# Then:
#   cd work/arda/telperion/examples/dbn/lean
#   lake exe cache get && lake build                        # the island; AxiomGuardDBN is a default target
#   lake env lean AxiomGuardDBN.lean | grep -E 'dbn_newman|selberg_newman'   # [propext, Classical.choice, Quot.sound]
#   cd ../../../missions/judge/dbn && lake build MissionChallenges.RH_dbn_newman MissionChallenges.RH_dbn_selberg_newman MissionChallenges.RH_dbn_selberg_newman_sharp
#   # optional second kernel: build leanprover/comparator at tag v4.34.0 with lean-toolchain v4.34.0-rc1 and
#   # nanoda, then `lake env comparator RH_dbn_newman.comparator.json` must accept (as CI did, logs/).
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
. <(grep -E '^(source_repo|source_commit|source_tag)=' "$HERE/provenance/ARDA_SOURCE")
mkdir -p "$HERE/work"; rm -rf "$HERE/work/arda"
git clone --no-checkout "$source_repo" "$HERE/work/arda"
git -C "$HERE/work/arda" checkout --detach "$source_commit"
[ "$(git -C "$HERE/work/arda" rev-parse "$source_tag^{commit}" 2>/dev/null || echo "$source_commit")" = "$source_commit" ] || { echo "tag/commit mismatch"; exit 1; }
for f in "$HERE"/lean/dbn/*.lean; do cmp -s "$f" "$HERE/work/arda/telperion/examples/dbn/lean/$(basename "$f")" || { echo "vendored copy differs from source: $f"; exit 1; }; done
for n in RH_dbn_newman RH_dbn_selberg_newman RH_dbn_selberg_newman_sharp; do cmp -s "$HERE/lean/judge/MissionChallenges/$n.lean" "$HERE/work/arda/telperion/missions/judge/dbn/MissionChallenges/$n.lean" || { echo "judge challenge differs: $n"; exit 1; }; done
echo "Materialized at $HERE/work/arda ($source_repo @ $source_commit, tag $source_tag); vendored copies verified byte-identical. See the header of this script for the build commands."
