// ======================================================================
// \title  PolymorphismStateMachineAc.hpp
// \author Generated by fpp-to-cpp
// \brief  hpp file for Polymorphism state machine
// ======================================================================

#ifndef FppTest_SmState_PolymorphismStateMachineAc_HPP
#define FppTest_SmState_PolymorphismStateMachineAc_HPP

#include <FpConfig.hpp>

#include "Fw/Types/ExternalString.hpp"
#include "Fw/Types/Serializable.hpp"
#include "Fw/Types/String.hpp"

namespace FppTest {

  namespace SmState {

    //! A hierarchical state machine with behavioral polymorphism
    class PolymorphismStateMachineBase {

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
          //! State S4
          S4,
          //! State S5
          S5,
        };

        //! The signal type
        enum class Signal : FwEnumStoreType {
          //! The initial transition
          __FPRIME_AC_INITIAL_TRANSITION,
          //! Signal for transition from S2 to S3
          S2_to_S3,
          //! Signal for polymorphic transition
          poly,
        };

      PROTECTED:

        // ----------------------------------------------------------------------
        // Constructors and Destructors
        // ----------------------------------------------------------------------

        //! Constructor
        PolymorphismStateMachineBase();

        //! Destructor
        virtual ~PolymorphismStateMachineBase();

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
        PolymorphismStateMachineBase::State getState() const;

      public:

        // ----------------------------------------------------------------------
        // Send signal functions
        // ----------------------------------------------------------------------

        //! Signal for polymorphic transition
        void sendSignal_poly();

        //! Signal for transition from S2 to S3
        void sendSignal_S2_to_S3();

      PRIVATE:

        // ----------------------------------------------------------------------
        // State and choice entry
        // ----------------------------------------------------------------------

        //! Enter state S5
        void enter_S5(
            Signal signal //!< The signal
        );

        //! Enter state S4
        void enter_S4(
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
