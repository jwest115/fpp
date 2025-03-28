// ======================================================================
// \title  SmChoiceActiveComponentAc.hpp
// \author Generated by fpp-to-cpp
// \brief  hpp file for SmChoiceActive component base class
// ======================================================================

#ifndef FppTest_SmChoiceActiveComponentAc_HPP
#define FppTest_SmChoiceActiveComponentAc_HPP

#include <Fw/FPrimeBasicTypes.hpp>

#include "Fw/Comp/ActiveComponentBase.hpp"
#include "Fw/Port/InputSerializePort.hpp"
#include "Fw/Port/OutputSerializePort.hpp"
#include "SmChoiceActive_BasicStateMachineAc.hpp"
#include "state-machine/choice/BasicStateMachineAc.hpp"
#include "state-machine/choice/BasicU32StateMachineAc.hpp"
#include "state-machine/choice/ChoiceToChoiceStateMachineAc.hpp"
#include "state-machine/choice/ChoiceToStateStateMachineAc.hpp"
#include "state-machine/choice/InputPairU16U32StateMachineAc.hpp"
#include "state-machine/choice/SequenceStateMachineAc.hpp"
#include "state-machine/choice/SequenceU32StateMachineAc.hpp"

namespace FppTest {

  //! \class SmChoiceActiveComponentBase
  //! \brief Auto-generated base for SmChoiceActive component
  class SmChoiceActiveComponentBase :
    public Fw::ActiveComponentBase
  {

      // ----------------------------------------------------------------------
      // Friend classes
      // ----------------------------------------------------------------------

      //! Friend class for white-box testing
      friend class SmChoiceActiveComponentBaseFriend;

    PROTECTED:

      // ----------------------------------------------------------------------
      // Constants
      // ----------------------------------------------------------------------

      //! State machine identifiers
      enum class SmId : FwEnumStoreType {
        basic,
        smChoiceBasic,
        smChoiceBasicU32,
        smChoiceChoiceToChoice,
        smChoiceChoiceToState,
        smChoiceInputPairU16U32,
        smChoiceSequence,
        smChoiceSequenceU32,
      };

    PROTECTED:

      // ----------------------------------------------------------------------
      // Types for internal state machines
      // ----------------------------------------------------------------------

      //! Implementation of state machine FppTest_SmChoice_Basic
      class FppTest_SmChoice_Basic :
        public FppTest::SmChoice::BasicStateMachineBase
      {

        public:

          //! Constructor
          FppTest_SmChoice_Basic(
              SmChoiceActiveComponentBase& component //!< The enclosing component
          );

        public:

          //! Initialize the state machine
          void init(
              SmChoiceActiveComponentBase::SmId smId //!< The state machine id
          );

        public:

          //! Get the state machine id
          SmChoiceActiveComponentBase::SmId getId() const;

        PRIVATE:

          //! Implementation for action a
          void action_a(
              Signal signal //!< The signal
          );

          //! Implementation for action b
          void action_b(
              Signal signal //!< The signal
          );

        PRIVATE:

          //! Implementation for guard g
          bool guard_g(
              Signal signal //!< The signal
          ) const;

        PRIVATE:

          //! The enclosing component
          SmChoiceActiveComponentBase& m_component;

      };

      //! Implementation of state machine FppTest_SmChoice_BasicU32
      class FppTest_SmChoice_BasicU32 :
        public FppTest::SmChoice::BasicU32StateMachineBase
      {

        public:

          //! Constructor
          FppTest_SmChoice_BasicU32(
              SmChoiceActiveComponentBase& component //!< The enclosing component
          );

        public:

          //! Initialize the state machine
          void init(
              SmChoiceActiveComponentBase::SmId smId //!< The state machine id
          );

        public:

          //! Get the state machine id
          SmChoiceActiveComponentBase::SmId getId() const;

        PRIVATE:

          //! Implementation for action a
          void action_a(
              Signal signal, //!< The signal
              U32 value //!< The value
          );

          //! Implementation for action b
          void action_b(
              Signal signal //!< The signal
          );

        PRIVATE:

          //! Implementation for guard g
          bool guard_g(
              Signal signal, //!< The signal
              U32 value //!< The value
          ) const;

        PRIVATE:

          //! The enclosing component
          SmChoiceActiveComponentBase& m_component;

      };

      //! Implementation of state machine FppTest_SmChoice_ChoiceToChoice
      class FppTest_SmChoice_ChoiceToChoice :
        public FppTest::SmChoice::ChoiceToChoiceStateMachineBase
      {

        public:

          //! Constructor
          FppTest_SmChoice_ChoiceToChoice(
              SmChoiceActiveComponentBase& component //!< The enclosing component
          );

        public:

          //! Initialize the state machine
          void init(
              SmChoiceActiveComponentBase::SmId smId //!< The state machine id
          );

        public:

          //! Get the state machine id
          SmChoiceActiveComponentBase::SmId getId() const;

        PRIVATE:

          //! Implementation for action exitS1
          void action_exitS1(
              Signal signal //!< The signal
          );

          //! Implementation for action a
          void action_a(
              Signal signal //!< The signal
          );

          //! Implementation for action enterS2
          void action_enterS2(
              Signal signal //!< The signal
          );

        PRIVATE:

          //! Implementation for guard g1
          bool guard_g1(
              Signal signal //!< The signal
          ) const;

          //! Implementation for guard g2
          bool guard_g2(
              Signal signal //!< The signal
          ) const;

        PRIVATE:

          //! The enclosing component
          SmChoiceActiveComponentBase& m_component;

      };

      //! Implementation of state machine FppTest_SmChoice_ChoiceToState
      class FppTest_SmChoice_ChoiceToState :
        public FppTest::SmChoice::ChoiceToStateStateMachineBase
      {

        public:

          //! Constructor
          FppTest_SmChoice_ChoiceToState(
              SmChoiceActiveComponentBase& component //!< The enclosing component
          );

        public:

          //! Initialize the state machine
          void init(
              SmChoiceActiveComponentBase::SmId smId //!< The state machine id
          );

        public:

          //! Get the state machine id
          SmChoiceActiveComponentBase::SmId getId() const;

        PRIVATE:

          //! Implementation for action exitS1
          void action_exitS1(
              Signal signal //!< The signal
          );

          //! Implementation for action a
          void action_a(
              Signal signal //!< The signal
          );

          //! Implementation for action enterS2
          void action_enterS2(
              Signal signal //!< The signal
          );

          //! Implementation for action enterS3
          void action_enterS3(
              Signal signal //!< The signal
          );

        PRIVATE:

          //! Implementation for guard g
          bool guard_g(
              Signal signal //!< The signal
          ) const;

        PRIVATE:

          //! The enclosing component
          SmChoiceActiveComponentBase& m_component;

      };

      //! Implementation of state machine FppTest_SmChoice_InputPairU16U32
      class FppTest_SmChoice_InputPairU16U32 :
        public FppTest::SmChoice::InputPairU16U32StateMachineBase
      {

        public:

          //! Constructor
          FppTest_SmChoice_InputPairU16U32(
              SmChoiceActiveComponentBase& component //!< The enclosing component
          );

        public:

          //! Initialize the state machine
          void init(
              SmChoiceActiveComponentBase::SmId smId //!< The state machine id
          );

        public:

          //! Get the state machine id
          SmChoiceActiveComponentBase::SmId getId() const;

        PRIVATE:

          //! Implementation for action a
          void action_a(
              Signal signal, //!< The signal
              U32 value //!< The value
          );

        PRIVATE:

          //! Implementation for guard g
          bool guard_g(
              Signal signal, //!< The signal
              U32 value //!< The value
          ) const;

        PRIVATE:

          //! The enclosing component
          SmChoiceActiveComponentBase& m_component;

      };

      //! Implementation of state machine FppTest_SmChoice_Sequence
      class FppTest_SmChoice_Sequence :
        public FppTest::SmChoice::SequenceStateMachineBase
      {

        public:

          //! Constructor
          FppTest_SmChoice_Sequence(
              SmChoiceActiveComponentBase& component //!< The enclosing component
          );

        public:

          //! Initialize the state machine
          void init(
              SmChoiceActiveComponentBase::SmId smId //!< The state machine id
          );

        public:

          //! Get the state machine id
          SmChoiceActiveComponentBase::SmId getId() const;

        PRIVATE:

          //! Implementation for action a
          void action_a(
              Signal signal //!< The signal
          );

          //! Implementation for action b
          void action_b(
              Signal signal //!< The signal
          );

        PRIVATE:

          //! Implementation for guard g1
          bool guard_g1(
              Signal signal //!< The signal
          ) const;

          //! Implementation for guard g2
          bool guard_g2(
              Signal signal //!< The signal
          ) const;

        PRIVATE:

          //! The enclosing component
          SmChoiceActiveComponentBase& m_component;

      };

      //! Implementation of state machine FppTest_SmChoice_SequenceU32
      class FppTest_SmChoice_SequenceU32 :
        public FppTest::SmChoice::SequenceU32StateMachineBase
      {

        public:

          //! Constructor
          FppTest_SmChoice_SequenceU32(
              SmChoiceActiveComponentBase& component //!< The enclosing component
          );

        public:

          //! Initialize the state machine
          void init(
              SmChoiceActiveComponentBase::SmId smId //!< The state machine id
          );

        public:

          //! Get the state machine id
          SmChoiceActiveComponentBase::SmId getId() const;

        PRIVATE:

          //! Implementation for action a
          void action_a(
              Signal signal, //!< The signal
              U32 value //!< The value
          );

          //! Implementation for action b
          void action_b(
              Signal signal //!< The signal
          );

        PRIVATE:

          //! Implementation for guard g1
          bool guard_g1(
              Signal signal //!< The signal
          ) const;

          //! Implementation for guard g2
          bool guard_g2(
              Signal signal, //!< The signal
              U32 value //!< The value
          ) const;

        PRIVATE:

          //! The enclosing component
          SmChoiceActiveComponentBase& m_component;

      };

      //! Implementation of state machine FppTest_SmChoiceActive_Basic
      class FppTest_SmChoiceActive_Basic :
        public FppTest::SmChoiceActive_BasicStateMachineBase
      {

        public:

          //! Constructor
          FppTest_SmChoiceActive_Basic(
              SmChoiceActiveComponentBase& component //!< The enclosing component
          );

        public:

          //! Initialize the state machine
          void init(
              SmChoiceActiveComponentBase::SmId smId //!< The state machine id
          );

        public:

          //! Get the state machine id
          SmChoiceActiveComponentBase::SmId getId() const;

        PRIVATE:

          //! Implementation for action a
          void action_a(
              Signal signal //!< The signal
          );

          //! Implementation for action b
          void action_b(
              Signal signal //!< The signal
          );

        PRIVATE:

          //! Implementation for guard g
          bool guard_g(
              Signal signal //!< The signal
          ) const;

        PRIVATE:

          //! The enclosing component
          SmChoiceActiveComponentBase& m_component;

      };

    public:

      // ----------------------------------------------------------------------
      // Component initialization
      // ----------------------------------------------------------------------

      //! Initialize SmChoiceActiveComponentBase object
      void init(
          FwSizeType queueDepth, //!< The queue depth
          FwEnumStoreType instance = 0 //!< The instance number
      );

    PROTECTED:

      // ----------------------------------------------------------------------
      // Component construction and destruction
      // ----------------------------------------------------------------------

      //! Construct SmChoiceActiveComponentBase object
      SmChoiceActiveComponentBase(
          const char* compName = "" //!< The component name
      );

      //! Destroy SmChoiceActiveComponentBase object
      virtual ~SmChoiceActiveComponentBase();

    PROTECTED:

      // ----------------------------------------------------------------------
      // State getter functions
      // ----------------------------------------------------------------------

      //! Get the state of state machine instance basic
      FppTest_SmChoiceActive_Basic::State basic_getState() const;

      //! Get the state of state machine instance smChoiceBasic
      FppTest_SmChoice_Basic::State smChoiceBasic_getState() const;

      //! Get the state of state machine instance smChoiceBasicU32
      FppTest_SmChoice_BasicU32::State smChoiceBasicU32_getState() const;

      //! Get the state of state machine instance smChoiceChoiceToChoice
      FppTest_SmChoice_ChoiceToChoice::State smChoiceChoiceToChoice_getState() const;

      //! Get the state of state machine instance smChoiceChoiceToState
      FppTest_SmChoice_ChoiceToState::State smChoiceChoiceToState_getState() const;

      //! Get the state of state machine instance smChoiceInputPairU16U32
      FppTest_SmChoice_InputPairU16U32::State smChoiceInputPairU16U32_getState() const;

      //! Get the state of state machine instance smChoiceSequence
      FppTest_SmChoice_Sequence::State smChoiceSequence_getState() const;

      //! Get the state of state machine instance smChoiceSequenceU32
      FppTest_SmChoice_SequenceU32::State smChoiceSequenceU32_getState() const;

    PROTECTED:

      // ----------------------------------------------------------------------
      // Signal send functions
      // ----------------------------------------------------------------------

      //! Send signal s to state machine basic
      void basic_sendSignal_s();

      //! Send signal s to state machine smChoiceBasic
      void smChoiceBasic_sendSignal_s();

      //! Send signal s to state machine smChoiceBasicU32
      void smChoiceBasicU32_sendSignal_s(
          U32 value //!< The value
      );

      //! Send signal s to state machine smChoiceChoiceToChoice
      void smChoiceChoiceToChoice_sendSignal_s();

      //! Send signal s to state machine smChoiceChoiceToState
      void smChoiceChoiceToState_sendSignal_s();

      //! Send signal s1 to state machine smChoiceInputPairU16U32
      void smChoiceInputPairU16U32_sendSignal_s1(
          U16 value //!< The value
      );

      //! Send signal s2 to state machine smChoiceInputPairU16U32
      void smChoiceInputPairU16U32_sendSignal_s2(
          U32 value //!< The value
      );

      //! Send signal s to state machine smChoiceSequence
      void smChoiceSequence_sendSignal_s();

      //! Send signal s to state machine smChoiceSequenceU32
      void smChoiceSequenceU32_sendSignal_s(
          U32 value //!< The value
      );

    PROTECTED:

      // ----------------------------------------------------------------------
      // Overflow hooks for internal state machine instances
      //
      // When sending a signal to a state machine instance, if
      // the queue overflows and the instance is marked with 'hook' behavior,
      // the corresponding function here is called.
      // ----------------------------------------------------------------------

      //! Overflow hook for state machine smChoiceChoiceToChoice
      virtual void smChoiceChoiceToChoice_stateMachineOverflowHook(
          SmId smId, //!< The state machine ID
          FwEnumStoreType signal, //!< The signal
          Fw::SerializeBufferBase& buffer //!< The message buffer
      ) = 0;

    PROTECTED:

      // ----------------------------------------------------------------------
      // Functions to implement for internal state machine actions
      // ----------------------------------------------------------------------

      //! Implementation for action a of state machine FppTest_SmChoice_Basic
      //!
      //! Action a
      virtual void FppTest_SmChoice_Basic_action_a(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_Basic::Signal signal //!< The signal
      ) = 0;

      //! Implementation for action b of state machine FppTest_SmChoice_Basic
      //!
      //! Action b
      virtual void FppTest_SmChoice_Basic_action_b(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_Basic::Signal signal //!< The signal
      ) = 0;

      //! Implementation for action a of state machine FppTest_SmChoice_BasicU32
      //!
      //! Action a
      virtual void FppTest_SmChoice_BasicU32_action_a(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_BasicU32::Signal signal, //!< The signal
          U32 value //!< The value
      ) = 0;

      //! Implementation for action b of state machine FppTest_SmChoice_BasicU32
      //!
      //! Action b
      virtual void FppTest_SmChoice_BasicU32_action_b(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_BasicU32::Signal signal //!< The signal
      ) = 0;

      //! Implementation for action exitS1 of state machine FppTest_SmChoice_ChoiceToChoice
      //!
      //! Exit S1
      virtual void FppTest_SmChoice_ChoiceToChoice_action_exitS1(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_ChoiceToChoice::Signal signal //!< The signal
      ) = 0;

      //! Implementation for action a of state machine FppTest_SmChoice_ChoiceToChoice
      //!
      //! Action a
      virtual void FppTest_SmChoice_ChoiceToChoice_action_a(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_ChoiceToChoice::Signal signal //!< The signal
      ) = 0;

      //! Implementation for action enterS2 of state machine FppTest_SmChoice_ChoiceToChoice
      //!
      //! Enter S2
      virtual void FppTest_SmChoice_ChoiceToChoice_action_enterS2(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_ChoiceToChoice::Signal signal //!< The signal
      ) = 0;

      //! Implementation for action exitS1 of state machine FppTest_SmChoice_ChoiceToState
      //!
      //! Exit S1
      virtual void FppTest_SmChoice_ChoiceToState_action_exitS1(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_ChoiceToState::Signal signal //!< The signal
      ) = 0;

      //! Implementation for action a of state machine FppTest_SmChoice_ChoiceToState
      //!
      //! Action a
      virtual void FppTest_SmChoice_ChoiceToState_action_a(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_ChoiceToState::Signal signal //!< The signal
      ) = 0;

      //! Implementation for action enterS2 of state machine FppTest_SmChoice_ChoiceToState
      //!
      //! Enter S2
      virtual void FppTest_SmChoice_ChoiceToState_action_enterS2(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_ChoiceToState::Signal signal //!< The signal
      ) = 0;

      //! Implementation for action enterS3 of state machine FppTest_SmChoice_ChoiceToState
      //!
      //! Enter S3
      virtual void FppTest_SmChoice_ChoiceToState_action_enterS3(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_ChoiceToState::Signal signal //!< The signal
      ) = 0;

      //! Implementation for action a of state machine FppTest_SmChoice_InputPairU16U32
      //!
      //! Action a
      virtual void FppTest_SmChoice_InputPairU16U32_action_a(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_InputPairU16U32::Signal signal, //!< The signal
          U32 value //!< The value
      ) = 0;

      //! Implementation for action a of state machine FppTest_SmChoice_Sequence
      //!
      //! Action a
      virtual void FppTest_SmChoice_Sequence_action_a(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_Sequence::Signal signal //!< The signal
      ) = 0;

      //! Implementation for action b of state machine FppTest_SmChoice_Sequence
      //!
      //! Action b
      virtual void FppTest_SmChoice_Sequence_action_b(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_Sequence::Signal signal //!< The signal
      ) = 0;

      //! Implementation for action a of state machine FppTest_SmChoice_SequenceU32
      //!
      //! Action a
      virtual void FppTest_SmChoice_SequenceU32_action_a(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_SequenceU32::Signal signal, //!< The signal
          U32 value //!< The value
      ) = 0;

      //! Implementation for action b of state machine FppTest_SmChoice_SequenceU32
      //!
      //! Action b
      virtual void FppTest_SmChoice_SequenceU32_action_b(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_SequenceU32::Signal signal //!< The signal
      ) = 0;

      //! Implementation for action a of state machine FppTest_SmChoiceActive_Basic
      //!
      //! Action a
      virtual void FppTest_SmChoiceActive_Basic_action_a(
          SmId smId, //!< The state machine id
          FppTest_SmChoiceActive_Basic::Signal signal //!< The signal
      ) = 0;

      //! Implementation for action b of state machine FppTest_SmChoiceActive_Basic
      //!
      //! Action b
      virtual void FppTest_SmChoiceActive_Basic_action_b(
          SmId smId, //!< The state machine id
          FppTest_SmChoiceActive_Basic::Signal signal //!< The signal
      ) = 0;

    PROTECTED:

      // ----------------------------------------------------------------------
      // Functions to implement for internal state machine guards
      // ----------------------------------------------------------------------

      //! Implementation for guard g of state machine FppTest_SmChoice_Basic
      //!
      //! Guard g
      virtual bool FppTest_SmChoice_Basic_guard_g(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_Basic::Signal signal //!< The signal
      ) const = 0;

      //! Implementation for guard g of state machine FppTest_SmChoice_BasicU32
      //!
      //! Guard g
      virtual bool FppTest_SmChoice_BasicU32_guard_g(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_BasicU32::Signal signal, //!< The signal
          U32 value //!< The value
      ) const = 0;

      //! Implementation for guard g1 of state machine FppTest_SmChoice_ChoiceToChoice
      //!
      //! Guard g1
      virtual bool FppTest_SmChoice_ChoiceToChoice_guard_g1(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_ChoiceToChoice::Signal signal //!< The signal
      ) const = 0;

      //! Implementation for guard g2 of state machine FppTest_SmChoice_ChoiceToChoice
      //!
      //! Guard g2
      virtual bool FppTest_SmChoice_ChoiceToChoice_guard_g2(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_ChoiceToChoice::Signal signal //!< The signal
      ) const = 0;

      //! Implementation for guard g of state machine FppTest_SmChoice_ChoiceToState
      //!
      //! Guard g
      virtual bool FppTest_SmChoice_ChoiceToState_guard_g(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_ChoiceToState::Signal signal //!< The signal
      ) const = 0;

      //! Implementation for guard g of state machine FppTest_SmChoice_InputPairU16U32
      //!
      //! Guard g
      virtual bool FppTest_SmChoice_InputPairU16U32_guard_g(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_InputPairU16U32::Signal signal, //!< The signal
          U32 value //!< The value
      ) const = 0;

      //! Implementation for guard g1 of state machine FppTest_SmChoice_Sequence
      //!
      //! Guard g1
      virtual bool FppTest_SmChoice_Sequence_guard_g1(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_Sequence::Signal signal //!< The signal
      ) const = 0;

      //! Implementation for guard g2 of state machine FppTest_SmChoice_Sequence
      //!
      //! Guard g2
      virtual bool FppTest_SmChoice_Sequence_guard_g2(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_Sequence::Signal signal //!< The signal
      ) const = 0;

      //! Implementation for guard g1 of state machine FppTest_SmChoice_SequenceU32
      //!
      //! Guard g1
      virtual bool FppTest_SmChoice_SequenceU32_guard_g1(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_SequenceU32::Signal signal //!< The signal
      ) const = 0;

      //! Implementation for guard g2 of state machine FppTest_SmChoice_SequenceU32
      //!
      //! Guard g2
      virtual bool FppTest_SmChoice_SequenceU32_guard_g2(
          SmId smId, //!< The state machine id
          FppTest_SmChoice_SequenceU32::Signal signal, //!< The signal
          U32 value //!< The value
      ) const = 0;

      //! Implementation for guard g of state machine FppTest_SmChoiceActive_Basic
      //!
      //! Guard g
      virtual bool FppTest_SmChoiceActive_Basic_guard_g(
          SmId smId, //!< The state machine id
          FppTest_SmChoiceActive_Basic::Signal signal //!< The signal
      ) const = 0;

    PRIVATE:

      // ----------------------------------------------------------------------
      // Message dispatch functions
      // ----------------------------------------------------------------------

      //! Called in the message loop to dispatch a message from the queue
      virtual MsgDispatchStatus doDispatch();

    PRIVATE:

      // ----------------------------------------------------------------------
      // Send signal helper functions
      // ----------------------------------------------------------------------

      //! Start sending a signal to a state machine
      void sendSignalStart(
          SmId smId, //!< The state machine ID (input)
          FwEnumStoreType signal, //!< The signal (input)
          Fw::SerializeBufferBase& buffer //!< The message buffer (output)
      );

      //! Finish sending a signal to a state machine
      void basic_sendSignalFinish(
          Fw::SerializeBufferBase& buffer //!< The buffer with the data to send
      );

      //! Finish sending a signal to a state machine
      void smChoiceBasic_sendSignalFinish(
          Fw::SerializeBufferBase& buffer //!< The buffer with the data to send
      );

      //! Finish sending a signal to a state machine
      void smChoiceBasicU32_sendSignalFinish(
          Fw::SerializeBufferBase& buffer //!< The buffer with the data to send
      );

      //! Finish sending a signal to a state machine
      void smChoiceChoiceToChoice_sendSignalFinish(
          Fw::SerializeBufferBase& buffer //!< The buffer with the data to send
      );

      //! Finish sending a signal to a state machine
      void smChoiceChoiceToState_sendSignalFinish(
          Fw::SerializeBufferBase& buffer //!< The buffer with the data to send
      );

      //! Finish sending a signal to a state machine
      void smChoiceInputPairU16U32_sendSignalFinish(
          Fw::SerializeBufferBase& buffer //!< The buffer with the data to send
      );

      //! Finish sending a signal to a state machine
      void smChoiceSequence_sendSignalFinish(
          Fw::SerializeBufferBase& buffer //!< The buffer with the data to send
      );

      //! Finish sending a signal to a state machine
      void smChoiceSequenceU32_sendSignalFinish(
          Fw::SerializeBufferBase& buffer //!< The buffer with the data to send
      );

    PRIVATE:

      // ----------------------------------------------------------------------
      // Helper functions for state machine dispatch
      // ----------------------------------------------------------------------

      //! Dispatch a signal to a state machine instance
      void smDispatch(
          Fw::SerializeBufferBase& buffer //!< The message buffer
      );

      //! Deserialize the state machine ID and signal from the message buffer
      static void deserializeSmIdAndSignal(
          Fw::SerializeBufferBase& buffer, //!< The message buffer (input and output)
          FwEnumStoreType& smId, //!< The state machine ID (output)
          FwEnumStoreType& signal //!< The signal (output)
      );

      //! Dispatch a signal to a state machine instance of type FppTest_SmChoice_Basic
      void FppTest_SmChoice_Basic_smDispatch(
          Fw::SerializeBufferBase& buffer, //!< The message buffer
          FppTest_SmChoice_Basic& sm, //!< The state machine
          FppTest_SmChoice_Basic::Signal signal //!< The signal
      );

      //! Dispatch a signal to a state machine instance of type FppTest_SmChoice_BasicU32
      void FppTest_SmChoice_BasicU32_smDispatch(
          Fw::SerializeBufferBase& buffer, //!< The message buffer
          FppTest_SmChoice_BasicU32& sm, //!< The state machine
          FppTest_SmChoice_BasicU32::Signal signal //!< The signal
      );

      //! Dispatch a signal to a state machine instance of type FppTest_SmChoice_ChoiceToChoice
      void FppTest_SmChoice_ChoiceToChoice_smDispatch(
          Fw::SerializeBufferBase& buffer, //!< The message buffer
          FppTest_SmChoice_ChoiceToChoice& sm, //!< The state machine
          FppTest_SmChoice_ChoiceToChoice::Signal signal //!< The signal
      );

      //! Dispatch a signal to a state machine instance of type FppTest_SmChoice_ChoiceToState
      void FppTest_SmChoice_ChoiceToState_smDispatch(
          Fw::SerializeBufferBase& buffer, //!< The message buffer
          FppTest_SmChoice_ChoiceToState& sm, //!< The state machine
          FppTest_SmChoice_ChoiceToState::Signal signal //!< The signal
      );

      //! Dispatch a signal to a state machine instance of type FppTest_SmChoice_InputPairU16U32
      void FppTest_SmChoice_InputPairU16U32_smDispatch(
          Fw::SerializeBufferBase& buffer, //!< The message buffer
          FppTest_SmChoice_InputPairU16U32& sm, //!< The state machine
          FppTest_SmChoice_InputPairU16U32::Signal signal //!< The signal
      );

      //! Dispatch a signal to a state machine instance of type FppTest_SmChoice_Sequence
      void FppTest_SmChoice_Sequence_smDispatch(
          Fw::SerializeBufferBase& buffer, //!< The message buffer
          FppTest_SmChoice_Sequence& sm, //!< The state machine
          FppTest_SmChoice_Sequence::Signal signal //!< The signal
      );

      //! Dispatch a signal to a state machine instance of type FppTest_SmChoice_SequenceU32
      void FppTest_SmChoice_SequenceU32_smDispatch(
          Fw::SerializeBufferBase& buffer, //!< The message buffer
          FppTest_SmChoice_SequenceU32& sm, //!< The state machine
          FppTest_SmChoice_SequenceU32::Signal signal //!< The signal
      );

      //! Dispatch a signal to a state machine instance of type FppTest_SmChoiceActive_Basic
      void FppTest_SmChoiceActive_Basic_smDispatch(
          Fw::SerializeBufferBase& buffer, //!< The message buffer
          FppTest_SmChoiceActive_Basic& sm, //!< The state machine
          FppTest_SmChoiceActive_Basic::Signal signal //!< The signal
      );

    PRIVATE:

      // ----------------------------------------------------------------------
      // State machine instances
      // ----------------------------------------------------------------------

      //! State machine basic
      FppTest_SmChoiceActive_Basic m_stateMachine_basic;

      //! State machine smChoiceBasic
      FppTest_SmChoice_Basic m_stateMachine_smChoiceBasic;

      //! State machine smChoiceBasicU32
      FppTest_SmChoice_BasicU32 m_stateMachine_smChoiceBasicU32;

      //! State machine smChoiceChoiceToChoice
      FppTest_SmChoice_ChoiceToChoice m_stateMachine_smChoiceChoiceToChoice;

      //! State machine smChoiceChoiceToState
      FppTest_SmChoice_ChoiceToState m_stateMachine_smChoiceChoiceToState;

      //! State machine smChoiceInputPairU16U32
      FppTest_SmChoice_InputPairU16U32 m_stateMachine_smChoiceInputPairU16U32;

      //! State machine smChoiceSequence
      FppTest_SmChoice_Sequence m_stateMachine_smChoiceSequence;

      //! State machine smChoiceSequenceU32
      FppTest_SmChoice_SequenceU32 m_stateMachine_smChoiceSequenceU32;

  };

}

#endif
