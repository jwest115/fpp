// ======================================================================
// \title  BasicInternalStateMachineAc.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for BasicInternal state machine
// ======================================================================

#include "Fw/Types/Assert.hpp"
#include "state-machine/state/BasicInternalStateMachineAc.hpp"

namespace FppTest {

  namespace SmState {

    // ----------------------------------------------------------------------
    // Constructors and Destructors
    // ----------------------------------------------------------------------

    BasicInternalStateMachineBase ::
      BasicInternalStateMachineBase()
    {

    }

    BasicInternalStateMachineBase ::
      ~BasicInternalStateMachineBase()
    {

    }

    // ----------------------------------------------------------------------
    // Initialization
    // ----------------------------------------------------------------------

    void BasicInternalStateMachineBase ::
      initBase(const FwEnumStoreType id)
    {
      this->m_id = id;
      this->enter_S(Signal::__FPRIME_AC_INITIAL_TRANSITION);
    }

    // ----------------------------------------------------------------------
    // Getter functions
    // ----------------------------------------------------------------------

    BasicInternalStateMachineBase::State BasicInternalStateMachineBase ::
      getState() const
    {
      return this->m_state;
    }

    // ----------------------------------------------------------------------
    // Send signal functions
    // ----------------------------------------------------------------------

    void BasicInternalStateMachineBase ::
      sendSignal_s()
    {
      switch (this->m_state) {
        case State::S:
          this->action_a(Signal::s);
          break;
        default:
          FW_ASSERT(0, static_cast<FwAssertArgType>(this->m_state));
          break;
      }
    }

    // ----------------------------------------------------------------------
    // State and choice entry
    // ----------------------------------------------------------------------

    void BasicInternalStateMachineBase ::
      enter_S(Signal signal)
    {
      this->action_a(signal);
      this->m_state = State::S;
    }

  }

}
