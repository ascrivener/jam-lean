#!/usr/bin/env bash
# Run a build command within the CI job's build budget (used by .github/workflows/build.yml).
#
# CI_DEADLINE (epoch seconds) is the time by which every build step must have stopped, so the job
# still has time to save .lake. If the command is cut off by that deadline (or the deadline has already
# passed), this records CI_TIMED_OUT=true in $GITHUB_ENV and exits 0: the run's next attempt job resumes
# from the saved .lake. Any other failure (a proof error, an out-of-memory kill) keeps its exit code.
set -u
: "${CI_DEADLINE:?CI_DEADLINE is not set}"

timed_out() {
  echo "::notice::build budget reached; the next attempt resumes from the saved .lake"
  echo "CI_TIMED_OUT=true" >> "${GITHUB_ENV:-/dev/null}"
  exit 0
}

remaining=$(( CI_DEADLINE - $(date +%s) ))
[ "$remaining" -gt 60 ] || timed_out

timeout --signal=INT --kill-after=2m "${remaining}s" "$@"
rc=$?
[ "$rc" -eq 0 ] && exit 0
# timeout exits 124 (or 137 after the follow-up KILL) when the deadline cut the command off; an
# earlier non-zero exit, including an OOM kill's 137, is a real failure.
if [ "$(date +%s)" -ge $(( CI_DEADLINE - 5 )) ]; then timed_out; fi
exit "$rc"
