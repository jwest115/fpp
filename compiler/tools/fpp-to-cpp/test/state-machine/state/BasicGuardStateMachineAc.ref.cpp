// ======================================================================
// \title  BasicGuardStateMachineAc.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for BasicGuard state machine
// ======================================================================

#include "Fw/Types/Assert.hpp"
#include "state-machine/state/BasicGuardStateMachineAc.hpp"

namespace FppTest {

  namespace SmState {

    // ----------------------------------------------------------------------
    // Constructors and Destructors
    // ----------------------------------------------------------------------

    BasicGuardStateMachineBase ::
      BasicGuardStateMachineBase()
    {

    }

    BasicGuardStateMachineBase ::
      ~BasicGuardStateMachineBase()
    {

    }

    // ----------------------------------------------------------------------
    // Initialization
    // ----------------------------------------------------------------------

    void BasicGuardStateMachineBase ::
      initBase(const FwEnumStoreType id)
    {
      this->m_id = id;
      this->enter_S(Signal::__FPRIME_AC_INITIAL_TRANSITION);
    }

    // ----------------------------------------------------------------------
    // Getter functions
    // ----------------------------------------------------------------------

    BasicGuardStateMachineBase::State BasicGuardStateMachineBase ::
      getState() const
    {
      return this->m_state;
    }

    // ----------------------------------------------------------------------
    // Send signal functions
    // ----------------------------------------------------------------------

    void BasicGuardStateMachineBase ::
      sendSignal_s()
    {
      switch (this->m_state) {
        case State::S:
          if (this->guard_g(Signal::s)) {
            this->action_a(Signal::s);
            this->action_a(Signal::s);
            this->action_a(Signal::s);
            this->enter_T(Signal::s);
          }
          break;
        case State::T:
          break;
        default:
          FW_ASSERT(0, static_cast<FwAssertArgType>(this->m_state));
          break;
      }
    }

    // ----------------------------------------------------------------------
    // State and choice entry
    // ----------------------------------------------------------------------

    void BasicGuardStateMachineBase ::
      enter_T(Signal signal)
    {
      this->action_a(signal);
      this->action_a(signal);
      this->action_a(signal);
      this->m_state = State::T;
    }

    void BasicGuardStateMachineBase ::
      enter_S(Signal signal)
    {
      this->m_state = State::S;
    }

  }

}
