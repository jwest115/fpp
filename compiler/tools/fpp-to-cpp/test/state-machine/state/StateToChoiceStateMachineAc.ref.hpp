// ======================================================================
// \title  StateToChoiceStateMachineAc.hpp
// \author Generated by fpp-to-cpp
// \brief  hpp file for StateToChoice state machine
// ======================================================================

#ifndef FppTest_SmState_StateToChoiceStateMachineAc_HPP
#define FppTest_SmState_StateToChoiceStateMachineAc_HPP

#include <Fw/FPrimeBasicTypes.hpp>

#include "Fw/Types/ExternalString.hpp"
#include "Fw/Types/Serializable.hpp"
#include "Fw/Types/String.hpp"

namespace FppTest {

  namespace SmState {

    //! A state machine for testing state-to-choice transitions
    //! with hierarchy
    class StateToChoiceStateMachineBase {

      public:

        // ----------------------------------------------------------------------
        // Types
        // ----------------------------------------------------------------------

        //! The state type
        enum class State : FwEnumStoreType {
          //! The uninitialized state
          __FPRIME_AC_UNINITIALIZED,
          //! State S2
          S1_S2,
          //! State S3
          S1_S3,
          //! State S5
          S4_S5,
          //! State S6
          S4_S6,
        };

        //! The signal type
        enum class Signal : FwEnumStoreType {
          //! The initial transition
          __FPRIME_AC_INITIAL_TRANSITION,
          //! Signal for going from S1 to C
          S1_to_C,
          //! Signal for going from S1 to S4
          S1_to_S4,
          //! Signal for going from S2 to S3
          S2_to_S3,
        };

      PROTECTED:

        // ----------------------------------------------------------------------
        // Constructors and Destructors
        // ----------------------------------------------------------------------

        //! Constructor
        StateToChoiceStateMachineBase();

        //! Destructor
        virtual ~StateToChoiceStateMachineBase();

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
        StateToChoiceStateMachineBase::State getState() const;

      public:

        // ----------------------------------------------------------------------
        // Send signal functions
        // ----------------------------------------------------------------------

        //! Signal for going from S1 to S4
        void sendSignal_S1_to_S4();

        //! Signal for going from S1 to C
        void sendSignal_S1_to_C();

        //! Signal for going from S2 to S3
        void sendSignal_S2_to_S3();

      PROTECTED:

        // ----------------------------------------------------------------------
        // Actions
        // ----------------------------------------------------------------------

        //! Exit S1
        virtual void action_exitS1(
            Signal signal //!< The signal
        ) = 0;

        //! Exit S2
        virtual void action_exitS2(
            Signal signal //!< The signal
        ) = 0;

        //! Exit S3
        virtual void action_exitS3(
            Signal signal //!< The signal
        ) = 0;

        //! Action a
        virtual void action_a(
            Signal signal //!< The signal
        ) = 0;

        //! Enter S1
        virtual void action_enterS1(
            Signal signal //!< The signal
        ) = 0;

        //! Enter S2
        virtual void action_enterS2(
            Signal signal //!< The signal
        ) = 0;

        //! Enter S3
        virtual void action_enterS3(
            Signal signal //!< The signal
        ) = 0;

        //! Enter S4
        virtual void action_enterS4(
            Signal signal //!< The signal
        ) = 0;

      PROTECTED:

        // ----------------------------------------------------------------------
        // Guards
        // ----------------------------------------------------------------------

        //! Guard g
        virtual bool guard_g(
            Signal signal //!< The signal
        ) const = 0;

      PRIVATE:

        // ----------------------------------------------------------------------
        // State and choice entry
        // ----------------------------------------------------------------------

        //! Enter state S4
        void enter_S4(
            Signal signal //!< The signal
        );

        //! Enter choice S4_C
        void enter_S4_C(
            Signal signal //!< The signal
        );

        //! Enter state S4_S5
        void enter_S4_S5(
            Signal signal //!< The signal
        );

        //! Enter state S4_S6
        void enter_S4_S6(
            Signal signal //!< The signal
        );

        //! Enter state S1
        void enter_S1(
            Signal signal //!< The signal
        );

        //! Enter state S1_S2
        void enter_S1_S2(
            Signal signal //!< The signal
        );

        //! Enter state S1_S3
        void enter_S1_S3(
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
