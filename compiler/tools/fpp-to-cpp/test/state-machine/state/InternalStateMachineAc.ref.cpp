// ======================================================================
// \title  InternalStateMachineAc.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for Internal state machine
// ======================================================================

#include "Fw/Types/Assert.hpp"
#include "state-machine/state/InternalStateMachineAc.hpp"

namespace FppTest {

  namespace SmState {

    // ----------------------------------------------------------------------
    // Constructors and Destructors
    // ----------------------------------------------------------------------

    InternalStateMachineBase ::
      InternalStateMachineBase()
    {

    }

    InternalStateMachineBase ::
      ~InternalStateMachineBase()
    {

    }

    // ----------------------------------------------------------------------
    // Initialization
    // ----------------------------------------------------------------------

    void InternalStateMachineBase ::
      initBase(const FwEnumStoreType id)
    {
      this->m_id = id;
      // Enter the initial target of the state machine
      this->enter_S1(Signal::__FPRIME_AC_INITIAL_TRANSITION);
    }

    // ----------------------------------------------------------------------
    // Getter functions
    // ----------------------------------------------------------------------

    InternalStateMachineBase::State InternalStateMachineBase ::
      getState() const
    {
      return this->m_state;
    }

    // ----------------------------------------------------------------------
    // Send signal functions
    // ----------------------------------------------------------------------

    void InternalStateMachineBase ::
      sendSignal_S1_internal()
    {
      switch (this->m_state) {
        case State::S1_S2:
          // Do the actions for the transition
          this->action_a(Signal::S1_internal);
          break;
        case State::S1_S3:
          // Do the actions for the transition
          this->action_a(Signal::S1_internal);
          break;
        default:
          FW_ASSERT(0, static_cast<FwAssertArgType>(this->m_state));
          break;
      }
    }

    void InternalStateMachineBase ::
      sendSignal_S2_to_S3()
    {
      switch (this->m_state) {
        case State::S1_S2:
          // Enter the target
          this->enter_S1_S3(Signal::S2_to_S3);
          break;
        case State::S1_S3:
          break;
        default:
          FW_ASSERT(0, static_cast<FwAssertArgType>(this->m_state));
          break;
      }
    }

    // ----------------------------------------------------------------------
    // State and choice entry
    // ----------------------------------------------------------------------

    void InternalStateMachineBase ::
      enter_S1(Signal signal)
    {
      // Enter the target of the initial transition
      this->enter_S1_S2(signal);
    }

    void InternalStateMachineBase ::
      enter_S1_S2(Signal signal)
    {
      // Update the state
      this->m_state = State::S1_S2;
    }

    void InternalStateMachineBase ::
      enter_S1_S3(Signal signal)
    {
      // Update the state
      this->m_state = State::S1_S3;
    }

  }

}
