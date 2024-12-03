// ======================================================================
// \title  StateToChildStateMachineAc.hpp
// \author Generated by fpp-to-cpp
// \brief  hpp file for StateToChild state machine
// ======================================================================

#ifndef FppTest_SmState_StateToChildStateMachineAc_HPP
#define FppTest_SmState_StateToChildStateMachineAc_HPP

#include <FpConfig.hpp>

#include "Fw/Types/ExternalString.hpp"
#include "Fw/Types/Serializable.hpp"
#include "Fw/Types/String.hpp"

namespace FppTest {

  namespace SmState {

    //! A state machine for testing state-to-child transitions
    class StateToChildStateMachineBase {

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
        };

        //! The signal type
        enum class Signal : FwEnumStoreType {
          //! The initial transition
          __FPRIME_AC_INITIAL_TRANSITION,
          //! Signal for going from S1 to S2
          S1_to_S2,
          //! Signal for going from S2 to S3
          S2_to_S3,
        };

      PROTECTED:

        // ----------------------------------------------------------------------
        // Constructors and Destructors
        // ----------------------------------------------------------------------

        //! Constructor
        StateToChildStateMachineBase();

        //! Destructor
        virtual ~StateToChildStateMachineBase();

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
        StateToChildStateMachineBase::State getState() const;

      public:

        // ----------------------------------------------------------------------
        // Send signal functions
        // ----------------------------------------------------------------------

        //! Signal for going from S1 to S2
        void sendSignal_S1_to_S2();

        //! Signal for going from S2 to S3
        void sendSignal_S2_to_S3();

      PROTECTED:

        // ----------------------------------------------------------------------
        // Actions
        // ----------------------------------------------------------------------

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

        //! Enter S2
        virtual void action_enterS2(
            Signal signal //!< The signal
        ) = 0;

        //! Enter S3
        virtual void action_enterS3(
            Signal signal //!< The signal
        ) = 0;

      PRIVATE:

        // ----------------------------------------------------------------------
        // State and choice entry
        // ----------------------------------------------------------------------

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
