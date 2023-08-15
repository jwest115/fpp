// ======================================================================
// \title  PassiveCommandsTester.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for PassiveCommands component test harness implementation class
// ======================================================================

#include "PassiveCommandsTester.hpp"

// ----------------------------------------------------------------------
// Construction and destruction
// ----------------------------------------------------------------------

PassiveCommandsTester ::
  PassiveCommandsTester() :
    PassiveCommandsGTestBase("PassiveCommandsTester", PassiveCommandsTester::MAX_HISTORY_SIZE),
    component("PassiveCommands")
{
  this->initComponents();
  this->connectPorts();
}

PassiveCommandsTester ::
  ~PassiveCommandsTester()
{

}

// ----------------------------------------------------------------------
// Tests
// ----------------------------------------------------------------------

void PassiveCommandsTester ::
  toDo()
{
  // TODO
}

// ----------------------------------------------------------------------
// Handlers for typed from ports
// ----------------------------------------------------------------------

void PassiveCommandsTester ::
  from_typedOut_handler(
      NATIVE_INT_TYPE portNum,
      U32 u32,
      F32 f32,
      bool b,
      const TypedPortStrings::StringSize80& str1,
      const E& e,
      const A& a,
      const S& s
  )
{
  // TODO
}

F32 PassiveCommandsTester ::
  from_typedReturnOut_handler(
      NATIVE_INT_TYPE portNum,
      U32 u32,
      F32 f32,
      bool b,
      const TypedReturnPortStrings::StringSize80& str2,
      const E& e,
      const A& a,
      const S& s
  )
{
  // TODO return
}