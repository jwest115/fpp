component_dir=`dirname $PWD`
fprime_dir=`dirname $component_dir`/fprime
test_dir=`dirname $component_dir`

empty()
{
  update "-t -i `cat ../deps-comma.txt`" "-p $component_dir,$fprime_dir ../empty" empty
  move_template Empty
}

passive()
{
  update "-t -i `cat ../deps-comma.txt`" "-p $component_dir,$fprime_dir ../passive" passive
  move_template PassiveCommands
  move_template PassiveEvents
  move_template PassiveGetProductPortsOnly
  move_template PassiveGetProducts
  move_template PassiveGuardedProducts
  move_template PassiveParams
  move_template PassiveExternalParams
  move_template PassiveSerial
  move_template PassiveSyncProductPortsOnly
  move_template PassiveSyncProducts
  move_template PassiveTelemetry
  move_template PassiveTest
}

active()
{
  update "-t -i `cat ../deps-comma.txt`" "-p $component_dir,$fprime_dir ../active" active
  move_template ActiveAsyncProductPortsOnly
  move_template ActiveAsyncProducts
  move_template ActiveCommands
  move_template ActiveOverflow
  move_template ActiveEvents
  move_template ActiveExternalStateMachines
  move_template ActiveGetProducts
  move_template ActiveGuardedProducts
  move_template ActiveNoArgsPortsOnly
  move_template ActiveParams
  move_template ActiveExternalParams
  move_template ActiveSerial
  move_template ActiveSyncProducts
  move_template ActiveTelemetry
  move_template ActiveTest
}

queued()
{
  update "-t -i `cat ../deps-comma.txt`" "-p $component_dir,$fprime_dir ../queued" queued
  move_template QueuedAsyncProductPortsOnly
  move_template QueuedAsyncProducts
  move_template QueuedCommands
  move_template QueuedOverflow
  move_template QueuedEvents
  move_template QueuedGetProducts
  move_template QueuedGuardedProducts
  move_template QueuedNoArgsPortsOnly
  move_template QueuedParams
  move_template QueuedExternalParams
  move_template QueuedSerial
  move_template QueuedSyncProducts
  move_template QueuedTelemetry
  move_template QueuedTest
}

sm_choice()
{
  update "-t -i `cat ../deps-comma.txt`,`cat ../sm-deps-comma.txt`" "-p $component_dir,$fprime_dir,$test_dir ../sm_choice" sm_choice
  move_template SmChoiceActive && \
  move_template SmChoiceQueued
}

sm_initial()
{
  update "-t -i `cat ../deps-comma.txt`,`cat ../sm-deps-comma.txt`" "-p $component_dir,$fprime_dir,$test_dir ../sm_initial" sm_initial
  move_template SmInitialActive
  move_template SmInitialQueued
}

sm_state()
{
  update "-t -i `cat ../deps-comma.txt`,`cat ../sm-deps-comma.txt`" "-p $component_dir,$fprime_dir,$test_dir ../sm_state" sm_state
  move_template SmStateActive
  move_template SmStateQueued
}
