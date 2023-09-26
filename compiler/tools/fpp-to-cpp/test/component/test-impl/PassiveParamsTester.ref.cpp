// ======================================================================
// \title  PassiveParamsTester.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for PassiveParams component test harness implementation class
// ======================================================================

#include "PassiveParamsTester.hpp"

// ----------------------------------------------------------------------
// Construction and destruction
// ----------------------------------------------------------------------

PassiveParamsTester ::
  PassiveParamsTester() :
    PassiveParamsGTestBase("PassiveParamsTester", PassiveParamsTester::MAX_HISTORY_SIZE),
    component("PassiveParams")
{
  this->initComponents();
  this->connectPorts();
}

PassiveParamsTester ::
  ~PassiveParamsTester()
{

}

// ----------------------------------------------------------------------
// Tests
// ----------------------------------------------------------------------

void PassiveParamsTester ::
  toDo()
{
  // TODO
}

// ----------------------------------------------------------------------
// Handlers for typed from ports
// ----------------------------------------------------------------------

void PassiveParamsTester ::
  from_noArgsOut_handler(NATIVE_INT_TYPE portNum)
{
  // TODO
}

void PassiveParamsTester ::
  from_typedOut_handler(
      NATIVE_INT_TYPE portNum,
      U32 u32,
      F32 f32,
      bool b,
      const Ports::TypedPortStrings::StringSize80& str1,
      const E& e,
      const A& a,
      const S& s
  )
{
  // TODO
}

F32 PassiveParamsTester ::
  from_typedReturnOut_handler(
      NATIVE_INT_TYPE portNum,
      U32 u32,
      F32 f32,
      bool b,
      const Ports::TypedReturnPortStrings::StringSize80& str2,
      const E& e,
      const A& a,
      const S& s
  )
{
  // TODO return
}
