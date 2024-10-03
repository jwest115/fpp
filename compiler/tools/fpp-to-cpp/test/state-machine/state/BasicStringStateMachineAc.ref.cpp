// ======================================================================
// \title  BasicStringStateMachineAc.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for BasicString state machine
// ======================================================================

#include "Fw/Types/Assert.hpp"
#include "state/BasicStringStateMachineAc.hpp"

namespace FppTest {

  namespace SmState {

    // ----------------------------------------------------------------------
    // Constructors and Destructors
    // ----------------------------------------------------------------------

    BasicStringStateMachineBase ::
      BasicStringStateMachineBase()
    {

    }

    BasicStringStateMachineBase ::
      ~BasicStringStateMachineBase()
    {

    }

    // ----------------------------------------------------------------------
    // Initialization
    // ----------------------------------------------------------------------

    void BasicStringStateMachineBase ::
      init(const FwEnumStoreType id)
    {
      this->m_id = id;
      this->enter_S(Signal::__FPRIME_AC_INITIAL_TRANSITION);
    }

    // ----------------------------------------------------------------------
    // Send signal functions
    // ----------------------------------------------------------------------

    void BasicStringStateMachineBase ::
      sendSignal_s(const Fw::StringBase& value)
    {
      switch (this->m_state) {
        case State::S:
          this->action_a(Signal::s);
          this->action_a(Signal::s);
          this->action_b(Signal::s, value);
          this->enter_T(Signal::s);
          break;
        case State::T:
          break;
        default:
          FW_ASSERT(0, static_cast<FwAssertArgType>(this->m_state));
          break;
      }
    }

    // ----------------------------------------------------------------------
    // State and junction entry
    // ----------------------------------------------------------------------

    void BasicStringStateMachineBase ::
      enter_T(Signal signal)
    {
      this->action_a(signal);
      this->action_a(signal);
      this->action_a(signal);
      this->m_state = State::T;
    }

    void BasicStringStateMachineBase ::
      enter_S(Signal signal)
    {
      this->m_state = State::S;
    }

  }

}