// ======================================================================
// \title  QueuedCommandsTester.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for QueuedCommands component test harness implementation class
// ======================================================================

#include "QueuedCommandsTester.hpp"

// ----------------------------------------------------------------------
// Construction and destruction
// ----------------------------------------------------------------------

QueuedCommandsTester ::
  QueuedCommandsTester() :
    QueuedCommandsGTestBase("QueuedCommandsTester", QueuedCommandsTester::MAX_HISTORY_SIZE),
    component("QueuedCommands")
{
  this->initComponents();
  this->connectPorts();
}

QueuedCommandsTester ::
  ~QueuedCommandsTester()
{

}

// ----------------------------------------------------------------------
// Tests
// ----------------------------------------------------------------------

void QueuedCommandsTester ::
  toDo()
{
  // TODO
}

// ----------------------------------------------------------------------
// Handlers for typed from ports
// ----------------------------------------------------------------------

void QueuedCommandsTester ::
  from_noArgsOut_handler(NATIVE_INT_TYPE portNum)
{
  // TODO
}

U32 QueuedCommandsTester ::
  from_noArgsReturnOut_handler(NATIVE_INT_TYPE portNum)
{
  // TODO return
}

void QueuedCommandsTester ::
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

F32 QueuedCommandsTester ::
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
