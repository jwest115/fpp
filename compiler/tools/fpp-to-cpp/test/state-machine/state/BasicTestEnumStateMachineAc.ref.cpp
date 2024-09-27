// ======================================================================
// \title  BasicTestEnumStateMachineAc.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for BasicTestEnum state machine
// ======================================================================

#include "Fw/Types/Assert.hpp"
#include "state/BasicTestEnumStateMachineAc.hpp"

namespace FppTest {

  namespace SmState {

    // ----------------------------------------------------------------------
    // Constructors and Destructors
    // ----------------------------------------------------------------------

    BasicTestEnumStateMachineBase ::
      BasicTestEnumStateMachineBase()
    {

    }

    BasicTestEnumStateMachineBase ::
      ~BasicTestEnumStateMachineBase()
    {

    }

    // ----------------------------------------------------------------------
    // Initialization
    // ----------------------------------------------------------------------

    void BasicTestEnumStateMachineBase ::
      init(const FwEnumStoreType id)
    {
      this->m_id = id;
      this->enter_S(Signal::__FPRIME_AC_INITIAL_TRANSITION);
    }

    // ----------------------------------------------------------------------
    // Send signal functions
    // ----------------------------------------------------------------------

    void BasicTestEnumStateMachineBase ::
      sendSignal_s(const FppTest::SmHarness::TestEnum& value)
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

    void BasicTestEnumStateMachineBase ::
      enter_T(Signal signal)
    {
      this->action_a(signal);
      this->action_a(signal);
      this->action_a(signal);
      this->m_state = State::T;
    }

    void BasicTestEnumStateMachineBase ::
      enter_S(Signal signal)
    {
      this->m_state = State::S;
    }

  }

}
