basic()
{
  update "-p $PWD" basic
  move_cpp BasicStateMachine
}

basic_self()
{
  update "-p $PWD" basic_self
  move_cpp BasicSelfStateMachine
}
