// ======================================================================
// \title  NoArgsReturnPortAc.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for NoArgsReturn port
// ======================================================================

#include "Fw/Types/Assert.hpp"
#include "Fw/Types/ExternalString.hpp"
#include "base/NoArgsReturnPortAc.hpp"

namespace Ports {

  // ----------------------------------------------------------------------
  // Input Port Member functions
  // ----------------------------------------------------------------------

  InputNoArgsReturnPort ::
    InputNoArgsReturnPort() :
      Fw::InputPortBase(),
      m_func(nullptr)
  {

  }

  void InputNoArgsReturnPort ::
    init()
  {
    Fw::InputPortBase::init();
  }

  void InputNoArgsReturnPort ::
    addCallComp(
        Fw::PassiveComponentBase* callComp,
        CompFuncPtr funcPtr
    )
  {
    FW_ASSERT(callComp != nullptr);
    FW_ASSERT(funcPtr != nullptr);

    this->m_comp = callComp;
    this->m_func = funcPtr;
    this->m_connObj = callComp;
  }

  U32 InputNoArgsReturnPort ::
    invoke()
  {
#if FW_PORT_TRACING == 1
    this->trace();
#endif

    FW_ASSERT(this->m_comp != nullptr);
    FW_ASSERT(this->m_func != nullptr);

    return this->m_func(this->m_comp, this->m_portNum);
  }

#if FW_PORT_SERIALIZATION == 1

  Fw::SerializeStatus InputNoArgsReturnPort ::
    invokeSerial(Fw::SerializeBufferBase& _buffer)
  {
    // For ports with a return type, invokeSerial is not used
    (void) _buffer;

    FW_ASSERT(0);
    return Fw::FW_SERIALIZE_OK;
  }

#endif

  // ----------------------------------------------------------------------
  // Output Port Member functions
  // ----------------------------------------------------------------------

  OutputNoArgsReturnPort ::
    OutputNoArgsReturnPort() :
      Fw::OutputPortBase(),
      m_port(nullptr)
  {

  }

  void OutputNoArgsReturnPort ::
    init()
  {
    Fw::OutputPortBase::init();
  }

  void OutputNoArgsReturnPort ::
    addCallPort(InputNoArgsReturnPort* callPort)
  {
    FW_ASSERT(callPort != nullptr);

    this->m_port = callPort;
    this->m_connObj = callPort;

#if FW_PORT_SERIALIZATION == 1
    this->m_serPort = nullptr;
#endif
  }

  U32 OutputNoArgsReturnPort ::
    invoke() const
  {
#if FW_PORT_TRACING == 1
    this->trace();
#endif

    FW_ASSERT(this->m_port != nullptr);
    return this->m_port->invoke();
  }

}
