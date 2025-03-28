// ======================================================================
// \title  BasicTestArrayStateMachineAc.hpp
// \author Generated by fpp-to-cpp
// \brief  hpp file for BasicTestArray state machine
// ======================================================================

#ifndef FppTest_SmState_BasicTestArrayStateMachineAc_HPP
#define FppTest_SmState_BasicTestArrayStateMachineAc_HPP

#include <Fw/FPrimeBasicTypes.hpp>

#include "Fw/Types/ExternalString.hpp"
#include "Fw/Types/Serializable.hpp"
#include "Fw/Types/String.hpp"
#include "state-machine/harness/TestArrayArrayAc.hpp"

namespace FppTest {

  namespace SmState {

    //! A basic state machine with TestArray actions
    class BasicTestArrayStateMachineBase {

      public:

        // ----------------------------------------------------------------------
        // Types
        // ----------------------------------------------------------------------

        //! The state type
        enum class State : FwEnumStoreType {
          //! The uninitialized state
          __FPRIME_AC_UNINITIALIZED,
          //! State S
          S,
          //! State T
          T,
        };

        //! The signal type
        enum class Signal : FwEnumStoreType {
          //! The initial transition
          __FPRIME_AC_INITIAL_TRANSITION,
          //! Signal s
          s,
        };

      PROTECTED:

        // ----------------------------------------------------------------------
        // Constructors and Destructors
        // ----------------------------------------------------------------------

        //! Constructor
        BasicTestArrayStateMachineBase();

        //! Destructor
        virtual ~BasicTestArrayStateMachineBase();

      protected:

        // ----------------------------------------------------------------------
        // Initialization
        // ----------------------------------------------------------------------

        //! Initialize the state machine
        void initBase(
            const FwEnumStoreType id //!< The state machine ID
        );

      public:

        // ----------------------------------------------------------------------
        // Getter functions
        // ----------------------------------------------------------------------

        //! Get the state
        BasicTestArrayStateMachineBase::State getState() const;

      public:

        // ----------------------------------------------------------------------
        // Send signal functions
        // ----------------------------------------------------------------------

        //! Signal s
        void sendSignal_s(
            const FppTest::SmHarness::TestArray& value //!< The value
        );

      PROTECTED:

        // ----------------------------------------------------------------------
        // Actions
        // ----------------------------------------------------------------------

        //! Action a
        virtual void action_a(
            Signal signal //!< The signal
        ) = 0;

        //! Action b
        virtual void action_b(
            Signal signal, //!< The signal
            const FppTest::SmHarness::TestArray& value //!< The value
        ) = 0;

      PRIVATE:

        // ----------------------------------------------------------------------
        // State and choice entry
        // ----------------------------------------------------------------------

        //! Enter state T
        void enter_T(
            Signal signal //!< The signal
        );

        //! Enter state S
        void enter_S(
            Signal signal //!< The signal
        );

      PROTECTED:

        // ----------------------------------------------------------------------
        // Member variables
        // ----------------------------------------------------------------------

        //! The state machine ID
        FwEnumStoreType m_id = 0;

        //! The state
        State m_state = State::__FPRIME_AC_UNINITIALIZED;

    };

  }

}

#endif
