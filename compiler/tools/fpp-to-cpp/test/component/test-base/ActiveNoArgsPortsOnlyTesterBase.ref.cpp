// ======================================================================
// \title  ActiveNoArgsPortsOnlyTesterBase.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for ActiveNoArgsPortsOnly component test harness base class
// ======================================================================

#include <cstdlib>
#include <cstring>

#include "test-base/ActiveNoArgsPortsOnlyTesterBase.hpp"

// ----------------------------------------------------------------------
// Component initialization
// ----------------------------------------------------------------------

void ActiveNoArgsPortsOnlyTesterBase ::
  init(FwEnumStoreType instance)
{
  // Initialize base class
  Fw::PassiveComponentBase::init(instance);

  // Connect input port noArgsOut
  for (
    FwIndexType port = 0;
    port < static_cast<FwIndexType>(this->getNum_from_noArgsOut());
    port++
  ) {
    this->m_from_noArgsOut[port].init();
    this->m_from_noArgsOut[port].addCallComp(
      this,
      from_noArgsOut_static
    );
    this->m_from_noArgsOut[port].setPortNum(port);

#if FW_OBJECT_NAMES == 1
    Fw::ObjectName portName;
    portName.format(
      "%s_from_noArgsOut[%" PRI_FwIndexType "]",
      this->m_objName.toChar(),
      port
    );
    this->m_from_noArgsOut[port].setObjName(portName.toChar());
#endif
  }

  // Connect input port noArgsReturnOut
  for (
    FwIndexType port = 0;
    port < static_cast<FwIndexType>(this->getNum_from_noArgsReturnOut());
    port++
  ) {
    this->m_from_noArgsReturnOut[port].init();
    this->m_from_noArgsReturnOut[port].addCallComp(
      this,
      from_noArgsReturnOut_static
    );
    this->m_from_noArgsReturnOut[port].setPortNum(port);

#if FW_OBJECT_NAMES == 1
    Fw::ObjectName portName;
    portName.format(
      "%s_from_noArgsReturnOut[%" PRI_FwIndexType "]",
      this->m_objName.toChar(),
      port
    );
    this->m_from_noArgsReturnOut[port].setObjName(portName.toChar());
#endif
  }

  // Connect output port noArgsAsync
  for (
    FwIndexType port = 0;
    port < static_cast<FwIndexType>(this->getNum_to_noArgsAsync());
    port++
  ) {
    this->m_to_noArgsAsync[port].init();

#if FW_OBJECT_NAMES == 1
    Fw::ObjectName portName;
    portName.format(
      "%s_to_noArgsAsync[%" PRI_FwIndexType "]",
      this->m_objName.toChar(),
      port
    );
    this->m_to_noArgsAsync[port].setObjName(portName.toChar());
#endif
  }

  // Connect output port noArgsGuarded
  for (
    FwIndexType port = 0;
    port < static_cast<FwIndexType>(this->getNum_to_noArgsGuarded());
    port++
  ) {
    this->m_to_noArgsGuarded[port].init();

#if FW_OBJECT_NAMES == 1
    Fw::ObjectName portName;
    portName.format(
      "%s_to_noArgsGuarded[%" PRI_FwIndexType "]",
      this->m_objName.toChar(),
      port
    );
    this->m_to_noArgsGuarded[port].setObjName(portName.toChar());
#endif
  }

  // Connect output port noArgsReturnGuarded
  for (
    FwIndexType port = 0;
    port < static_cast<FwIndexType>(this->getNum_to_noArgsReturnGuarded());
    port++
  ) {
    this->m_to_noArgsReturnGuarded[port].init();

#if FW_OBJECT_NAMES == 1
    Fw::ObjectName portName;
    portName.format(
      "%s_to_noArgsReturnGuarded[%" PRI_FwIndexType "]",
      this->m_objName.toChar(),
      port
    );
    this->m_to_noArgsReturnGuarded[port].setObjName(portName.toChar());
#endif
  }

  // Connect output port noArgsReturnSync
  for (
    FwIndexType port = 0;
    port < static_cast<FwIndexType>(this->getNum_to_noArgsReturnSync());
    port++
  ) {
    this->m_to_noArgsReturnSync[port].init();

#if FW_OBJECT_NAMES == 1
    Fw::ObjectName portName;
    portName.format(
      "%s_to_noArgsReturnSync[%" PRI_FwIndexType "]",
      this->m_objName.toChar(),
      port
    );
    this->m_to_noArgsReturnSync[port].setObjName(portName.toChar());
#endif
  }
}

// ----------------------------------------------------------------------
// Connectors for to ports
// ----------------------------------------------------------------------

void ActiveNoArgsPortsOnlyTesterBase ::
  connect_to_noArgsAsync(
      FwIndexType portNum,
      Ports::InputNoArgsPort* port
  )
{
  FW_ASSERT(
    (0 <= portNum) && (portNum < this->getNum_to_noArgsAsync()),
    static_cast<FwAssertArgType>(portNum)
  );

  this->m_to_noArgsAsync[portNum].addCallPort(port);
}

void ActiveNoArgsPortsOnlyTesterBase ::
  connect_to_noArgsGuarded(
      FwIndexType portNum,
      Ports::InputNoArgsPort* port
  )
{
  FW_ASSERT(
    (0 <= portNum) && (portNum < this->getNum_to_noArgsGuarded()),
    static_cast<FwAssertArgType>(portNum)
  );

  this->m_to_noArgsGuarded[portNum].addCallPort(port);
}

void ActiveNoArgsPortsOnlyTesterBase ::
  connect_to_noArgsReturnGuarded(
      FwIndexType portNum,
      Ports::InputNoArgsReturnPort* port
  )
{
  FW_ASSERT(
    (0 <= portNum) && (portNum < this->getNum_to_noArgsReturnGuarded()),
    static_cast<FwAssertArgType>(portNum)
  );

  this->m_to_noArgsReturnGuarded[portNum].addCallPort(port);
}

void ActiveNoArgsPortsOnlyTesterBase ::
  connect_to_noArgsReturnSync(
      FwIndexType portNum,
      Ports::InputNoArgsReturnPort* port
  )
{
  FW_ASSERT(
    (0 <= portNum) && (portNum < this->getNum_to_noArgsReturnSync()),
    static_cast<FwAssertArgType>(portNum)
  );

  this->m_to_noArgsReturnSync[portNum].addCallPort(port);
}

// ----------------------------------------------------------------------
// Getters for from ports
// ----------------------------------------------------------------------

Ports::InputNoArgsPort* ActiveNoArgsPortsOnlyTesterBase ::
  get_from_noArgsOut(FwIndexType portNum)
{
  FW_ASSERT(
    (0 <= portNum) && (portNum < this->getNum_from_noArgsOut()),
    static_cast<FwAssertArgType>(portNum)
  );

  return &this->m_from_noArgsOut[portNum];
}

Ports::InputNoArgsReturnPort* ActiveNoArgsPortsOnlyTesterBase ::
  get_from_noArgsReturnOut(FwIndexType portNum)
{
  FW_ASSERT(
    (0 <= portNum) && (portNum < this->getNum_from_noArgsReturnOut()),
    static_cast<FwAssertArgType>(portNum)
  );

  return &this->m_from_noArgsReturnOut[portNum];
}

// ----------------------------------------------------------------------
// Component construction and destruction
// ----------------------------------------------------------------------

ActiveNoArgsPortsOnlyTesterBase ::
  ActiveNoArgsPortsOnlyTesterBase(
      const char* const compName,
      const U32 maxHistorySize
  ) :
    Fw::PassiveComponentBase(compName)
{
  // Initialize port histories

  // Clear history
  this->clearHistory();
}

ActiveNoArgsPortsOnlyTesterBase ::
  ~ActiveNoArgsPortsOnlyTesterBase()
{
  // Destroy port histories
}

// ----------------------------------------------------------------------
// Default handler implementations for typed from ports
// You can override these implementation with more specific behavior
// ----------------------------------------------------------------------

void ActiveNoArgsPortsOnlyTesterBase ::
  from_noArgsOut_handler(FwIndexType portNum)
{
  this->pushFromPortEntry_noArgsOut();
}

U32 ActiveNoArgsPortsOnlyTesterBase ::
  from_noArgsReturnOut_handler(FwIndexType portNum)
{
  this->pushFromPortEntry_noArgsReturnOut();
  return 0;
}

// ----------------------------------------------------------------------
// Handler base-class functions for from ports
// ----------------------------------------------------------------------

void ActiveNoArgsPortsOnlyTesterBase ::
  from_noArgsOut_handlerBase(FwIndexType portNum)
{
  // Make sure port number is valid
  FW_ASSERT(
    (0 <= portNum) && (portNum < this->getNum_from_noArgsOut()),
    static_cast<FwAssertArgType>(portNum)
  );
  this->from_noArgsOut_handler(portNum);
}

U32 ActiveNoArgsPortsOnlyTesterBase ::
  from_noArgsReturnOut_handlerBase(FwIndexType portNum)
{
  // Make sure port number is valid
  FW_ASSERT(
    (0 <= portNum) && (portNum < this->getNum_from_noArgsReturnOut()),
    static_cast<FwAssertArgType>(portNum)
  );
  return this->from_noArgsReturnOut_handler(portNum);
}

// ----------------------------------------------------------------------
// Invocation functions for to ports
// ----------------------------------------------------------------------

void ActiveNoArgsPortsOnlyTesterBase ::
  invoke_to_noArgsAsync(FwIndexType portNum)
{
  // Make sure port number is valid
  FW_ASSERT(
    (0 <= portNum) && (portNum < this->getNum_to_noArgsAsync()),
    static_cast<FwAssertArgType>(portNum)
  );
  this->m_to_noArgsAsync[portNum].invoke();
}

void ActiveNoArgsPortsOnlyTesterBase ::
  invoke_to_noArgsGuarded(FwIndexType portNum)
{
  // Make sure port number is valid
  FW_ASSERT(
    (0 <= portNum) && (portNum < this->getNum_to_noArgsGuarded()),
    static_cast<FwAssertArgType>(portNum)
  );
  this->m_to_noArgsGuarded[portNum].invoke();
}

U32 ActiveNoArgsPortsOnlyTesterBase ::
  invoke_to_noArgsReturnGuarded(FwIndexType portNum)
{
  // Make sure port number is valid
  FW_ASSERT(
    (0 <= portNum) && (portNum < this->getNum_to_noArgsReturnGuarded()),
    static_cast<FwAssertArgType>(portNum)
  );
  return this->m_to_noArgsReturnGuarded[portNum].invoke();
}

U32 ActiveNoArgsPortsOnlyTesterBase ::
  invoke_to_noArgsReturnSync(FwIndexType portNum)
{
  // Make sure port number is valid
  FW_ASSERT(
    (0 <= portNum) && (portNum < this->getNum_to_noArgsReturnSync()),
    static_cast<FwAssertArgType>(portNum)
  );
  return this->m_to_noArgsReturnSync[portNum].invoke();
}

// ----------------------------------------------------------------------
// Getters for port counts
// ----------------------------------------------------------------------

FwIndexType ActiveNoArgsPortsOnlyTesterBase ::
  getNum_to_noArgsAsync() const
{
  return static_cast<FwIndexType>(FW_NUM_ARRAY_ELEMENTS(this->m_to_noArgsAsync));
}

FwIndexType ActiveNoArgsPortsOnlyTesterBase ::
  getNum_to_noArgsGuarded() const
{
  return static_cast<FwIndexType>(FW_NUM_ARRAY_ELEMENTS(this->m_to_noArgsGuarded));
}

FwIndexType ActiveNoArgsPortsOnlyTesterBase ::
  getNum_to_noArgsReturnGuarded() const
{
  return static_cast<FwIndexType>(FW_NUM_ARRAY_ELEMENTS(this->m_to_noArgsReturnGuarded));
}

FwIndexType ActiveNoArgsPortsOnlyTesterBase ::
  getNum_to_noArgsReturnSync() const
{
  return static_cast<FwIndexType>(FW_NUM_ARRAY_ELEMENTS(this->m_to_noArgsReturnSync));
}

FwIndexType ActiveNoArgsPortsOnlyTesterBase ::
  getNum_from_noArgsOut() const
{
  return static_cast<FwIndexType>(FW_NUM_ARRAY_ELEMENTS(this->m_from_noArgsOut));
}

FwIndexType ActiveNoArgsPortsOnlyTesterBase ::
  getNum_from_noArgsReturnOut() const
{
  return static_cast<FwIndexType>(FW_NUM_ARRAY_ELEMENTS(this->m_from_noArgsReturnOut));
}

// ----------------------------------------------------------------------
// Connection status queries for to ports
// ----------------------------------------------------------------------

bool ActiveNoArgsPortsOnlyTesterBase ::
  isConnected_to_noArgsAsync(FwIndexType portNum)
{
  FW_ASSERT(
    (0 <= portNum) && (portNum < this->getNum_to_noArgsAsync()),
    static_cast<FwAssertArgType>(portNum)
  );

  return this->m_to_noArgsAsync[portNum].isConnected();
}

bool ActiveNoArgsPortsOnlyTesterBase ::
  isConnected_to_noArgsGuarded(FwIndexType portNum)
{
  FW_ASSERT(
    (0 <= portNum) && (portNum < this->getNum_to_noArgsGuarded()),
    static_cast<FwAssertArgType>(portNum)
  );

  return this->m_to_noArgsGuarded[portNum].isConnected();
}

bool ActiveNoArgsPortsOnlyTesterBase ::
  isConnected_to_noArgsReturnGuarded(FwIndexType portNum)
{
  FW_ASSERT(
    (0 <= portNum) && (portNum < this->getNum_to_noArgsReturnGuarded()),
    static_cast<FwAssertArgType>(portNum)
  );

  return this->m_to_noArgsReturnGuarded[portNum].isConnected();
}

bool ActiveNoArgsPortsOnlyTesterBase ::
  isConnected_to_noArgsReturnSync(FwIndexType portNum)
{
  FW_ASSERT(
    (0 <= portNum) && (portNum < this->getNum_to_noArgsReturnSync()),
    static_cast<FwAssertArgType>(portNum)
  );

  return this->m_to_noArgsReturnSync[portNum].isConnected();
}

// ----------------------------------------------------------------------
// History functions
// ----------------------------------------------------------------------

void ActiveNoArgsPortsOnlyTesterBase ::
  clearHistory()
{
  this->clearFromPortHistory();
}

void ActiveNoArgsPortsOnlyTesterBase ::
  clearFromPortHistory()
{
  this->fromPortHistorySize = 0;
  this->fromPortHistorySize_noArgsOut = 0;
  this->fromPortHistorySize_noArgsReturnOut = 0;
}

void ActiveNoArgsPortsOnlyTesterBase ::
  pushFromPortEntry_noArgsOut()
{
  this->fromPortHistorySize_noArgsOut++;
  this->fromPortHistorySize++;
}

void ActiveNoArgsPortsOnlyTesterBase ::
  pushFromPortEntry_noArgsReturnOut()
{
  this->fromPortHistorySize_noArgsReturnOut++;
  this->fromPortHistorySize++;
}

// ----------------------------------------------------------------------
// Dispatching helper functions
// ----------------------------------------------------------------------

ActiveNoArgsPortsOnlyComponentBase::MsgDispatchStatus ActiveNoArgsPortsOnlyTesterBase ::
  dispatchOne(ActiveNoArgsPortsOnlyComponentBase& component)
{
      // Dispatch one message returning status
      return component.doDispatch();
}

ActiveNoArgsPortsOnlyComponentBase::MsgDispatchStatus ActiveNoArgsPortsOnlyTesterBase ::
  dispatchCurrentMessages(ActiveNoArgsPortsOnlyComponentBase& component)
{
      // Dispatch all current messages unless ERROR or EXIT occur
      const FwSizeType currentMessageCount = component.m_queue.getMessagesAvailable();
      ActiveNoArgsPortsOnlyComponentBase::MsgDispatchStatus messageStatus = ActiveNoArgsPortsOnlyComponentBase::MsgDispatchStatus::MSG_DISPATCH_EMPTY;
      for (FwSizeType i = 0; i < currentMessageCount; i++) {
          messageStatus = component.doDispatch();
          if (messageStatus != ActiveNoArgsPortsOnlyComponentBase::MSG_DISPATCH_OK) {
              break;
          }
      }
      return messageStatus;
}

// ----------------------------------------------------------------------
// Static functions for output ports
// ----------------------------------------------------------------------

void ActiveNoArgsPortsOnlyTesterBase ::
  from_noArgsOut_static(
      Fw::PassiveComponentBase* const callComp,
      FwIndexType portNum
  )
{
  FW_ASSERT(callComp != nullptr);
  ActiveNoArgsPortsOnlyTesterBase* _testerBase = static_cast<ActiveNoArgsPortsOnlyTesterBase*>(callComp);
  _testerBase->from_noArgsOut_handlerBase(portNum);
}

U32 ActiveNoArgsPortsOnlyTesterBase ::
  from_noArgsReturnOut_static(
      Fw::PassiveComponentBase* const callComp,
      FwIndexType portNum
  )
{
  FW_ASSERT(callComp != nullptr);
  ActiveNoArgsPortsOnlyTesterBase* _testerBase = static_cast<ActiveNoArgsPortsOnlyTesterBase*>(callComp);
  return _testerBase->from_noArgsReturnOut_handlerBase(portNum);
}
