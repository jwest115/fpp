// ======================================================================
// \title  SequenceStateMachineAc.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for Sequence state machine
// ======================================================================

#include "Fw/Types/Assert.hpp"
#include "state-machine/choice/SequenceStateMachineAc.hpp"

namespace FppTest {

  namespace SmChoice {

    // ----------------------------------------------------------------------
    // Constructors and Destructors
    // ----------------------------------------------------------------------

    SequenceStateMachineBase ::
      SequenceStateMachineBase()
    {

    }

    SequenceStateMachineBase ::
      ~SequenceStateMachineBase()
    {

    }

    // ----------------------------------------------------------------------
    // Initialization
    // ----------------------------------------------------------------------

    void SequenceStateMachineBase ::
      initBase(const FwEnumStoreType id)
    {
      this->m_id = id;
      // Enter the initial target of the state machine
      this->enter_S1(Signal::__FPRIME_AC_INITIAL_TRANSITION);
    }

    // ----------------------------------------------------------------------
    // Getter functions
    // ----------------------------------------------------------------------

    SequenceStateMachineBase::State SequenceStateMachineBase ::
      getState() const
    {
      return this->m_state;
    }

    // ----------------------------------------------------------------------
    // Send signal functions
    // ----------------------------------------------------------------------

    void SequenceStateMachineBase ::
      sendSignal_s()
    {
      switch (this->m_state) {
        case State::S1:
          // Enter the target
          this->enter_C1(Signal::s);
          break;
        case State::S2:
          break;
        case State::S3:
          break;
        case State::S4:
          break;
        default:
          FW_ASSERT(0, static_cast<FwAssertArgType>(this->m_state));
          break;
      }
    }

    // ----------------------------------------------------------------------
    // State and choice entry
    // ----------------------------------------------------------------------

    void SequenceStateMachineBase ::
      enter_S4(Signal signal)
    {
      // Update the state
      this->m_state = State::S4;
    }

    void SequenceStateMachineBase ::
      enter_S3(Signal signal)
    {
      // Update the state
      this->m_state = State::S3;
    }

    void SequenceStateMachineBase ::
      enter_S2(Signal signal)
    {
      // Update the state
      this->m_state = State::S2;
    }

    void SequenceStateMachineBase ::
      enter_C2(Signal signal)
    {
      if (this->guard_g2(signal)) {
        // Do the actions for the transition
        this->action_a(signal);
        // Enter the target
        this->enter_S3(signal);
      }
      else {
        // Do the actions for the transition
        this->action_b(signal);
        // Enter the target
        this->enter_S4(signal);
      }
    }

    void SequenceStateMachineBase ::
      enter_C1(Signal signal)
    {
      if (this->guard_g1(signal)) {
        // Enter the target
        this->enter_S2(signal);
      }
      else {
        // Enter the target
        this->enter_C2(signal);
      }
    }

    void SequenceStateMachineBase ::
      enter_S1(Signal signal)
    {
      // Update the state
      this->m_state = State::S1;
    }

  }

}
