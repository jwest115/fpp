. ./fpp-flags.sh

basic()
{
  run_test "$fpp_flags" Basic && \
    diff_cpp BasicStateMachine
}

basic_u32()
{
  run_test "$fpp_flags" BasicU32 && \
    diff_cpp BasicU32StateMachine
}