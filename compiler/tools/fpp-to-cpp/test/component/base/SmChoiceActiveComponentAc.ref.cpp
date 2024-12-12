// ======================================================================
// \title  SmChoiceActiveComponentAc.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for SmChoiceActive component base class
// ======================================================================

#include "Fw/Types/Assert.hpp"
#include "Fw/Types/ExternalString.hpp"
#if FW_ENABLE_TEXT_LOGGING
#include "Fw/Types/String.hpp"
#endif
#include "base/SmChoiceActiveComponentAc.hpp"

namespace FppTest {

  namespace {

    // Constant definitions for the state machine signal buffer
    namespace SmSignalBuffer {

      // Union for computing the max size of a signal type
      union SignalTypeUnion {
        BYTE size_of_U16[sizeof(U16)];
        BYTE size_of_U32[sizeof(U32)];
      };

      // The serialized size
      static constexpr FwSizeType SERIALIZED_SIZE =
        2 * sizeof(FwEnumStoreType) +
        sizeof(SignalTypeUnion);

    }

    enum MsgTypeEnum {
      SMCHOICEACTIVE_COMPONENT_EXIT = Fw::ActiveComponentBase::ACTIVE_COMPONENT_EXIT,
      INTERNAL_STATE_MACHINE_SIGNAL,
    };

    // Get the max size by constructing a union of the async input, command, and
    // internal port serialization sizes
    union BuffUnion {
      // Size of buffer for internal state machine signals
      // The internal SmSignalBuffer stores the state machine id, the
      // signal id, and the signal data
      BYTE internalSmBufferSize[SmSignalBuffer::SERIALIZED_SIZE];
    };

    // Define a message buffer class large enough to handle all the
    // asynchronous inputs to the component
    class ComponentIpcSerializableBuffer :
      public Fw::SerializeBufferBase
    {

      public:

        enum {
          // Offset into data in buffer: Size of message ID and port number
          DATA_OFFSET = sizeof(FwEnumStoreType) + sizeof(FwIndexType),
          // Max data size
          MAX_DATA_SIZE = sizeof(BuffUnion),
          // Max message size: Size of message id + size of port + max data size
          SERIALIZATION_SIZE = DATA_OFFSET + MAX_DATA_SIZE
        };

        Fw::Serializable::SizeType getBuffCapacity() const {
          return sizeof(m_buff);
        }

        U8* getBuffAddr() {
          return m_buff;
        }

        const U8* getBuffAddr() const {
          return m_buff;
        }

      private:
        // Should be the max of all the input ports serialized sizes...
        U8 m_buff[SERIALIZATION_SIZE];

    };
  }

  // ----------------------------------------------------------------------
  // Types for internal state machines
  // ----------------------------------------------------------------------

  SmChoiceActiveComponentBase::FppTest_SmChoice_Basic ::
    FppTest_SmChoice_Basic(SmChoiceActiveComponentBase& component) :
      m_component(component)
  {

  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_Basic ::
    init(SmChoiceActiveComponentBase::SmId smId)
  {
    this->initBase(static_cast<FwEnumStoreType>(smId));
  }

  SmChoiceActiveComponentBase::SmId SmChoiceActiveComponentBase::FppTest_SmChoice_Basic ::
    getId() const
  {
    return static_cast<SmChoiceActiveComponentBase::SmId>(this->m_id);
  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_Basic ::
    action_a(Signal signal)
  {
    this->m_component.FppTest_SmChoice_Basic_action_a(this->getId(), signal);
  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_Basic ::
    action_b(Signal signal)
  {
    this->m_component.FppTest_SmChoice_Basic_action_b(this->getId(), signal);
  }

  bool SmChoiceActiveComponentBase::FppTest_SmChoice_Basic ::
    guard_g(Signal signal) const
  {
    return this->m_component.FppTest_SmChoice_Basic_guard_g(this->getId(), signal);
  }

  SmChoiceActiveComponentBase::FppTest_SmChoice_BasicU32 ::
    FppTest_SmChoice_BasicU32(SmChoiceActiveComponentBase& component) :
      m_component(component)
  {

  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_BasicU32 ::
    init(SmChoiceActiveComponentBase::SmId smId)
  {
    this->initBase(static_cast<FwEnumStoreType>(smId));
  }

  SmChoiceActiveComponentBase::SmId SmChoiceActiveComponentBase::FppTest_SmChoice_BasicU32 ::
    getId() const
  {
    return static_cast<SmChoiceActiveComponentBase::SmId>(this->m_id);
  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_BasicU32 ::
    action_a(
        Signal signal,
        U32 value
    )
  {
    this->m_component.FppTest_SmChoice_BasicU32_action_a(this->getId(), signal, value);
  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_BasicU32 ::
    action_b(Signal signal)
  {
    this->m_component.FppTest_SmChoice_BasicU32_action_b(this->getId(), signal);
  }

  bool SmChoiceActiveComponentBase::FppTest_SmChoice_BasicU32 ::
    guard_g(
        Signal signal,
        U32 value
    ) const
  {
    return this->m_component.FppTest_SmChoice_BasicU32_guard_g(this->getId(), signal, value);
  }

  SmChoiceActiveComponentBase::FppTest_SmChoice_ChoiceToChoice ::
    FppTest_SmChoice_ChoiceToChoice(SmChoiceActiveComponentBase& component) :
      m_component(component)
  {

  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_ChoiceToChoice ::
    init(SmChoiceActiveComponentBase::SmId smId)
  {
    this->initBase(static_cast<FwEnumStoreType>(smId));
  }

  SmChoiceActiveComponentBase::SmId SmChoiceActiveComponentBase::FppTest_SmChoice_ChoiceToChoice ::
    getId() const
  {
    return static_cast<SmChoiceActiveComponentBase::SmId>(this->m_id);
  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_ChoiceToChoice ::
    action_exitS1(Signal signal)
  {
    this->m_component.FppTest_SmChoice_ChoiceToChoice_action_exitS1(this->getId(), signal);
  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_ChoiceToChoice ::
    action_a(Signal signal)
  {
    this->m_component.FppTest_SmChoice_ChoiceToChoice_action_a(this->getId(), signal);
  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_ChoiceToChoice ::
    action_enterS2(Signal signal)
  {
    this->m_component.FppTest_SmChoice_ChoiceToChoice_action_enterS2(this->getId(), signal);
  }

  bool SmChoiceActiveComponentBase::FppTest_SmChoice_ChoiceToChoice ::
    guard_g1(Signal signal) const
  {
    return this->m_component.FppTest_SmChoice_ChoiceToChoice_guard_g1(this->getId(), signal);
  }

  bool SmChoiceActiveComponentBase::FppTest_SmChoice_ChoiceToChoice ::
    guard_g2(Signal signal) const
  {
    return this->m_component.FppTest_SmChoice_ChoiceToChoice_guard_g2(this->getId(), signal);
  }

  SmChoiceActiveComponentBase::FppTest_SmChoice_ChoiceToState ::
    FppTest_SmChoice_ChoiceToState(SmChoiceActiveComponentBase& component) :
      m_component(component)
  {

  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_ChoiceToState ::
    init(SmChoiceActiveComponentBase::SmId smId)
  {
    this->initBase(static_cast<FwEnumStoreType>(smId));
  }

  SmChoiceActiveComponentBase::SmId SmChoiceActiveComponentBase::FppTest_SmChoice_ChoiceToState ::
    getId() const
  {
    return static_cast<SmChoiceActiveComponentBase::SmId>(this->m_id);
  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_ChoiceToState ::
    action_exitS1(Signal signal)
  {
    this->m_component.FppTest_SmChoice_ChoiceToState_action_exitS1(this->getId(), signal);
  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_ChoiceToState ::
    action_a(Signal signal)
  {
    this->m_component.FppTest_SmChoice_ChoiceToState_action_a(this->getId(), signal);
  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_ChoiceToState ::
    action_enterS2(Signal signal)
  {
    this->m_component.FppTest_SmChoice_ChoiceToState_action_enterS2(this->getId(), signal);
  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_ChoiceToState ::
    action_enterS3(Signal signal)
  {
    this->m_component.FppTest_SmChoice_ChoiceToState_action_enterS3(this->getId(), signal);
  }

  bool SmChoiceActiveComponentBase::FppTest_SmChoice_ChoiceToState ::
    guard_g(Signal signal) const
  {
    return this->m_component.FppTest_SmChoice_ChoiceToState_guard_g(this->getId(), signal);
  }

  SmChoiceActiveComponentBase::FppTest_SmChoice_InputPairU16U32 ::
    FppTest_SmChoice_InputPairU16U32(SmChoiceActiveComponentBase& component) :
      m_component(component)
  {

  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_InputPairU16U32 ::
    init(SmChoiceActiveComponentBase::SmId smId)
  {
    this->initBase(static_cast<FwEnumStoreType>(smId));
  }

  SmChoiceActiveComponentBase::SmId SmChoiceActiveComponentBase::FppTest_SmChoice_InputPairU16U32 ::
    getId() const
  {
    return static_cast<SmChoiceActiveComponentBase::SmId>(this->m_id);
  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_InputPairU16U32 ::
    action_a(
        Signal signal,
        U32 value
    )
  {
    this->m_component.FppTest_SmChoice_InputPairU16U32_action_a(this->getId(), signal, value);
  }

  bool SmChoiceActiveComponentBase::FppTest_SmChoice_InputPairU16U32 ::
    guard_g(
        Signal signal,
        U32 value
    ) const
  {
    return this->m_component.FppTest_SmChoice_InputPairU16U32_guard_g(this->getId(), signal, value);
  }

  SmChoiceActiveComponentBase::FppTest_SmChoice_Sequence ::
    FppTest_SmChoice_Sequence(SmChoiceActiveComponentBase& component) :
      m_component(component)
  {

  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_Sequence ::
    init(SmChoiceActiveComponentBase::SmId smId)
  {
    this->initBase(static_cast<FwEnumStoreType>(smId));
  }

  SmChoiceActiveComponentBase::SmId SmChoiceActiveComponentBase::FppTest_SmChoice_Sequence ::
    getId() const
  {
    return static_cast<SmChoiceActiveComponentBase::SmId>(this->m_id);
  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_Sequence ::
    action_a(Signal signal)
  {
    this->m_component.FppTest_SmChoice_Sequence_action_a(this->getId(), signal);
  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_Sequence ::
    action_b(Signal signal)
  {
    this->m_component.FppTest_SmChoice_Sequence_action_b(this->getId(), signal);
  }

  bool SmChoiceActiveComponentBase::FppTest_SmChoice_Sequence ::
    guard_g1(Signal signal) const
  {
    return this->m_component.FppTest_SmChoice_Sequence_guard_g1(this->getId(), signal);
  }

  bool SmChoiceActiveComponentBase::FppTest_SmChoice_Sequence ::
    guard_g2(Signal signal) const
  {
    return this->m_component.FppTest_SmChoice_Sequence_guard_g2(this->getId(), signal);
  }

  SmChoiceActiveComponentBase::FppTest_SmChoice_SequenceU32 ::
    FppTest_SmChoice_SequenceU32(SmChoiceActiveComponentBase& component) :
      m_component(component)
  {

  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_SequenceU32 ::
    init(SmChoiceActiveComponentBase::SmId smId)
  {
    this->initBase(static_cast<FwEnumStoreType>(smId));
  }

  SmChoiceActiveComponentBase::SmId SmChoiceActiveComponentBase::FppTest_SmChoice_SequenceU32 ::
    getId() const
  {
    return static_cast<SmChoiceActiveComponentBase::SmId>(this->m_id);
  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_SequenceU32 ::
    action_a(
        Signal signal,
        U32 value
    )
  {
    this->m_component.FppTest_SmChoice_SequenceU32_action_a(this->getId(), signal, value);
  }

  void SmChoiceActiveComponentBase::FppTest_SmChoice_SequenceU32 ::
    action_b(Signal signal)
  {
    this->m_component.FppTest_SmChoice_SequenceU32_action_b(this->getId(), signal);
  }

  bool SmChoiceActiveComponentBase::FppTest_SmChoice_SequenceU32 ::
    guard_g1(Signal signal) const
  {
    return this->m_component.FppTest_SmChoice_SequenceU32_guard_g1(this->getId(), signal);
  }

  bool SmChoiceActiveComponentBase::FppTest_SmChoice_SequenceU32 ::
    guard_g2(
        Signal signal,
        U32 value
    ) const
  {
    return this->m_component.FppTest_SmChoice_SequenceU32_guard_g2(this->getId(), signal, value);
  }

  SmChoiceActiveComponentBase::FppTest_SmChoiceActive_Basic ::
    FppTest_SmChoiceActive_Basic(SmChoiceActiveComponentBase& component) :
      m_component(component)
  {

  }

  void SmChoiceActiveComponentBase::FppTest_SmChoiceActive_Basic ::
    init(SmChoiceActiveComponentBase::SmId smId)
  {
    this->initBase(static_cast<FwEnumStoreType>(smId));
  }

  SmChoiceActiveComponentBase::SmId SmChoiceActiveComponentBase::FppTest_SmChoiceActive_Basic ::
    getId() const
  {
    return static_cast<SmChoiceActiveComponentBase::SmId>(this->m_id);
  }

  void SmChoiceActiveComponentBase::FppTest_SmChoiceActive_Basic ::
    action_a(Signal signal)
  {
    this->m_component.FppTest_SmChoiceActive_Basic_action_a(this->getId(), signal);
  }

  void SmChoiceActiveComponentBase::FppTest_SmChoiceActive_Basic ::
    action_b(Signal signal)
  {
    this->m_component.FppTest_SmChoiceActive_Basic_action_b(this->getId(), signal);
  }

  bool SmChoiceActiveComponentBase::FppTest_SmChoiceActive_Basic ::
    guard_g(Signal signal) const
  {
    return this->m_component.FppTest_SmChoiceActive_Basic_guard_g(this->getId(), signal);
  }

  // ----------------------------------------------------------------------
  // Component initialization
  // ----------------------------------------------------------------------

  void SmChoiceActiveComponentBase ::
    init(
        FwSizeType queueDepth,
        FwEnumStoreType instance
    )
  {
    // Initialize base class
    Fw::ActiveComponentBase::init(instance);

    // Initialize state machine instances
    this->m_stateMachine_basic.init(SmId::basic);
    this->m_stateMachine_smChoiceBasic.init(SmId::smChoiceBasic);
    this->m_stateMachine_smChoiceBasicU32.init(SmId::smChoiceBasicU32);
    this->m_stateMachine_smChoiceChoiceToChoice.init(SmId::smChoiceChoiceToChoice);
    this->m_stateMachine_smChoiceChoiceToState.init(SmId::smChoiceChoiceToState);
    this->m_stateMachine_smChoiceInputPairU16U32.init(SmId::smChoiceInputPairU16U32);
    this->m_stateMachine_smChoiceSequence.init(SmId::smChoiceSequence);
    this->m_stateMachine_smChoiceSequenceU32.init(SmId::smChoiceSequenceU32);

    // Create the queue
    Os::Queue::Status qStat = this->createQueue(
      queueDepth,
      static_cast<FwSizeType>(ComponentIpcSerializableBuffer::SERIALIZATION_SIZE)
    );
    FW_ASSERT(
      Os::Queue::Status::OP_OK == qStat,
      static_cast<FwAssertArgType>(qStat)
    );
  }

  // ----------------------------------------------------------------------
  // Component construction and destruction
  // ----------------------------------------------------------------------

  SmChoiceActiveComponentBase ::
    SmChoiceActiveComponentBase(const char* compName) :
      Fw::ActiveComponentBase(compName),
      m_stateMachine_basic(*this),
      m_stateMachine_smChoiceBasic(*this),
      m_stateMachine_smChoiceBasicU32(*this),
      m_stateMachine_smChoiceChoiceToChoice(*this),
      m_stateMachine_smChoiceChoiceToState(*this),
      m_stateMachine_smChoiceInputPairU16U32(*this),
      m_stateMachine_smChoiceSequence(*this),
      m_stateMachine_smChoiceSequenceU32(*this)
  {

  }

  SmChoiceActiveComponentBase ::
    ~SmChoiceActiveComponentBase()
  {

  }

  // ----------------------------------------------------------------------
  // State getter functions
  // ----------------------------------------------------------------------

  SmChoiceActiveComponentBase::FppTest_SmChoiceActive_Basic::State SmChoiceActiveComponentBase ::
    basic_getState() const
  {
    return this->m_stateMachine_basic.getState();
  }

  SmChoiceActiveComponentBase::FppTest_SmChoice_Basic::State SmChoiceActiveComponentBase ::
    smChoiceBasic_getState() const
  {
    return this->m_stateMachine_smChoiceBasic.getState();
  }

  SmChoiceActiveComponentBase::FppTest_SmChoice_BasicU32::State SmChoiceActiveComponentBase ::
    smChoiceBasicU32_getState() const
  {
    return this->m_stateMachine_smChoiceBasicU32.getState();
  }

  SmChoiceActiveComponentBase::FppTest_SmChoice_ChoiceToChoice::State SmChoiceActiveComponentBase ::
    smChoiceChoiceToChoice_getState() const
  {
    return this->m_stateMachine_smChoiceChoiceToChoice.getState();
  }

  SmChoiceActiveComponentBase::FppTest_SmChoice_ChoiceToState::State SmChoiceActiveComponentBase ::
    smChoiceChoiceToState_getState() const
  {
    return this->m_stateMachine_smChoiceChoiceToState.getState();
  }

  SmChoiceActiveComponentBase::FppTest_SmChoice_InputPairU16U32::State SmChoiceActiveComponentBase ::
    smChoiceInputPairU16U32_getState() const
  {
    return this->m_stateMachine_smChoiceInputPairU16U32.getState();
  }

  SmChoiceActiveComponentBase::FppTest_SmChoice_Sequence::State SmChoiceActiveComponentBase ::
    smChoiceSequence_getState() const
  {
    return this->m_stateMachine_smChoiceSequence.getState();
  }

  SmChoiceActiveComponentBase::FppTest_SmChoice_SequenceU32::State SmChoiceActiveComponentBase ::
    smChoiceSequenceU32_getState() const
  {
    return this->m_stateMachine_smChoiceSequenceU32.getState();
  }

  // ----------------------------------------------------------------------
  // Signal send functions
  // ----------------------------------------------------------------------

  void SmChoiceActiveComponentBase ::
    basic_sendSignal_s()
  {
    ComponentIpcSerializableBuffer buffer;
    // Serialize the message type, port number, state ID, and signal
    this->sendSignalStart(SmId::basic, static_cast<FwEnumStoreType>(FppTest_SmChoiceActive_Basic::Signal::s), buffer);
    // Send the message and handle overflow
    this->basic_sendSignalFinish(buffer);
  }

  void SmChoiceActiveComponentBase ::
    smChoiceBasic_sendSignal_s()
  {
    ComponentIpcSerializableBuffer buffer;
    // Serialize the message type, port number, state ID, and signal
    this->sendSignalStart(SmId::smChoiceBasic, static_cast<FwEnumStoreType>(FppTest_SmChoice_Basic::Signal::s), buffer);
    // Send the message and handle overflow
    this->smChoiceBasic_sendSignalFinish(buffer);
  }

  void SmChoiceActiveComponentBase ::
    smChoiceBasicU32_sendSignal_s(U32 value)
  {
    ComponentIpcSerializableBuffer buffer;
    // Serialize the message type, port number, state ID, and signal
    this->sendSignalStart(SmId::smChoiceBasicU32, static_cast<FwEnumStoreType>(FppTest_SmChoice_BasicU32::Signal::s), buffer);
    // Serialize the signal data
    const Fw::SerializeStatus status = buffer.serialize(value);
    FW_ASSERT(status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(status));
    // Send the message and handle overflow
    this->smChoiceBasicU32_sendSignalFinish(buffer);
  }

  void SmChoiceActiveComponentBase ::
    smChoiceChoiceToChoice_sendSignal_s()
  {
    ComponentIpcSerializableBuffer buffer;
    // Serialize the message type, port number, state ID, and signal
    this->sendSignalStart(SmId::smChoiceChoiceToChoice, static_cast<FwEnumStoreType>(FppTest_SmChoice_ChoiceToChoice::Signal::s), buffer);
    // Send the message and handle overflow
    this->smChoiceChoiceToChoice_sendSignalFinish(buffer);
  }

  void SmChoiceActiveComponentBase ::
    smChoiceChoiceToState_sendSignal_s()
  {
    ComponentIpcSerializableBuffer buffer;
    // Serialize the message type, port number, state ID, and signal
    this->sendSignalStart(SmId::smChoiceChoiceToState, static_cast<FwEnumStoreType>(FppTest_SmChoice_ChoiceToState::Signal::s), buffer);
    // Send the message and handle overflow
    this->smChoiceChoiceToState_sendSignalFinish(buffer);
  }

  void SmChoiceActiveComponentBase ::
    smChoiceInputPairU16U32_sendSignal_s1(U16 value)
  {
    ComponentIpcSerializableBuffer buffer;
    // Serialize the message type, port number, state ID, and signal
    this->sendSignalStart(SmId::smChoiceInputPairU16U32, static_cast<FwEnumStoreType>(FppTest_SmChoice_InputPairU16U32::Signal::s1), buffer);
    // Serialize the signal data
    const Fw::SerializeStatus status = buffer.serialize(value);
    FW_ASSERT(status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(status));
    // Send the message and handle overflow
    this->smChoiceInputPairU16U32_sendSignalFinish(buffer);
  }

  void SmChoiceActiveComponentBase ::
    smChoiceInputPairU16U32_sendSignal_s2(U32 value)
  {
    ComponentIpcSerializableBuffer buffer;
    // Serialize the message type, port number, state ID, and signal
    this->sendSignalStart(SmId::smChoiceInputPairU16U32, static_cast<FwEnumStoreType>(FppTest_SmChoice_InputPairU16U32::Signal::s2), buffer);
    // Serialize the signal data
    const Fw::SerializeStatus status = buffer.serialize(value);
    FW_ASSERT(status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(status));
    // Send the message and handle overflow
    this->smChoiceInputPairU16U32_sendSignalFinish(buffer);
  }

  void SmChoiceActiveComponentBase ::
    smChoiceSequence_sendSignal_s()
  {
    ComponentIpcSerializableBuffer buffer;
    // Serialize the message type, port number, state ID, and signal
    this->sendSignalStart(SmId::smChoiceSequence, static_cast<FwEnumStoreType>(FppTest_SmChoice_Sequence::Signal::s), buffer);
    // Send the message and handle overflow
    this->smChoiceSequence_sendSignalFinish(buffer);
  }

  void SmChoiceActiveComponentBase ::
    smChoiceSequenceU32_sendSignal_s(U32 value)
  {
    ComponentIpcSerializableBuffer buffer;
    // Serialize the message type, port number, state ID, and signal
    this->sendSignalStart(SmId::smChoiceSequenceU32, static_cast<FwEnumStoreType>(FppTest_SmChoice_SequenceU32::Signal::s), buffer);
    // Serialize the signal data
    const Fw::SerializeStatus status = buffer.serialize(value);
    FW_ASSERT(status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(status));
    // Send the message and handle overflow
    this->smChoiceSequenceU32_sendSignalFinish(buffer);
  }

  // ----------------------------------------------------------------------
  // Message dispatch functions
  // ----------------------------------------------------------------------

  Fw::QueuedComponentBase::MsgDispatchStatus SmChoiceActiveComponentBase ::
    doDispatch()
  {
    ComponentIpcSerializableBuffer msg;
    FwQueuePriorityType priority = 0;

    Os::Queue::Status msgStatus = this->m_queue.receive(
      msg,
      Os::Queue::BLOCKING,
      priority
    );
    FW_ASSERT(
      msgStatus == Os::Queue::OP_OK,
      static_cast<FwAssertArgType>(msgStatus)
    );

    // Reset to beginning of buffer
    msg.resetDeser();

    FwEnumStoreType desMsg = 0;
    Fw::SerializeStatus deserStatus = msg.deserialize(desMsg);
    FW_ASSERT(
      deserStatus == Fw::FW_SERIALIZE_OK,
      static_cast<FwAssertArgType>(deserStatus)
    );

    MsgTypeEnum msgType = static_cast<MsgTypeEnum>(desMsg);

    if (msgType == SMCHOICEACTIVE_COMPONENT_EXIT) {
      return MSG_DISPATCH_EXIT;
    }

    FwIndexType portNum = 0;
    deserStatus = msg.deserialize(portNum);
    FW_ASSERT(
      deserStatus == Fw::FW_SERIALIZE_OK,
      static_cast<FwAssertArgType>(deserStatus)
    );

    switch (msgType) {

      // Handle signals to internal state machines
      case INTERNAL_STATE_MACHINE_SIGNAL:
        this->smDispatch(msg);
        break;

      default:
        return MSG_DISPATCH_ERROR;
    }

    return MSG_DISPATCH_OK;
  }

  // ----------------------------------------------------------------------
  // Send signal helper functions
  // ----------------------------------------------------------------------

  void SmChoiceActiveComponentBase ::
    sendSignalStart(
        SmId smId,
        FwEnumStoreType signal,
        Fw::SerializeBufferBase& buffer
    )
  {
    Fw::SerializeStatus status = Fw::FW_SERIALIZE_OK;

    // Serialize the message type
    status = buffer.serialize(static_cast<FwEnumStoreType>(INTERNAL_STATE_MACHINE_SIGNAL));
    FW_ASSERT (status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(status));

    // Serialize the port number
    status = buffer.serialize(static_cast<FwIndexType>(0));
    FW_ASSERT (status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(status));

    // Serialize the state machine ID
    status = buffer.serialize(static_cast<FwEnumStoreType>(smId));
    FW_ASSERT (status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(status));

    // Serialize the signal
    status = buffer.serialize(static_cast<FwEnumStoreType>(signal));
    FW_ASSERT(status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(status));
  }

  void SmChoiceActiveComponentBase ::
    basic_sendSignalFinish(Fw::SerializeBufferBase& buffer)
  {
    // Send message
    Os::Queue::BlockingType _block = Os::Queue::NONBLOCKING;
    Os::Queue::Status qStatus = this->m_queue.send(buffer, 0, _block);

    FW_ASSERT(
      qStatus == Os::Queue::OP_OK,
      static_cast<FwAssertArgType>(qStatus)
    );
  }

  void SmChoiceActiveComponentBase ::
    smChoiceBasic_sendSignalFinish(Fw::SerializeBufferBase& buffer)
  {
    // Send message
    Os::Queue::BlockingType _block = Os::Queue::NONBLOCKING;
    Os::Queue::Status qStatus = this->m_queue.send(buffer, 1, _block);

    FW_ASSERT(
      qStatus == Os::Queue::OP_OK,
      static_cast<FwAssertArgType>(qStatus)
    );
  }

  void SmChoiceActiveComponentBase ::
    smChoiceBasicU32_sendSignalFinish(Fw::SerializeBufferBase& buffer)
  {
    // Send message
    Os::Queue::BlockingType _block = Os::Queue::BLOCKING;
    Os::Queue::Status qStatus = this->m_queue.send(buffer, 2, _block);

    FW_ASSERT(
      qStatus == Os::Queue::OP_OK,
      static_cast<FwAssertArgType>(qStatus)
    );
  }

  void SmChoiceActiveComponentBase ::
    smChoiceChoiceToChoice_sendSignalFinish(Fw::SerializeBufferBase& buffer)
  {
    // Send message
    Os::Queue::BlockingType _block = Os::Queue::NONBLOCKING;
    Os::Queue::Status qStatus = this->m_queue.send(buffer, 4, _block);

    if (qStatus == Os::Queue::Status::FULL) {

      // Deserialize the state machine ID and signal
      FwEnumStoreType smId;
      FwEnumStoreType signal;
      SmChoiceActiveComponentBase::deserializeSmIdAndSignal(buffer, smId, signal);

      // Call the overflow hook
      this->smChoiceChoiceToChoice_stateMachineOverflowHook(static_cast<SmId>(smId), signal, buffer);

      // Continue execution
      return;

    }

    FW_ASSERT(
      qStatus == Os::Queue::OP_OK,
      static_cast<FwAssertArgType>(qStatus)
    );
  }

  void SmChoiceActiveComponentBase ::
    smChoiceChoiceToState_sendSignalFinish(Fw::SerializeBufferBase& buffer)
  {
    // Send message
    Os::Queue::BlockingType _block = Os::Queue::NONBLOCKING;
    Os::Queue::Status qStatus = this->m_queue.send(buffer, 0, _block);

    FW_ASSERT(
      qStatus == Os::Queue::OP_OK,
      static_cast<FwAssertArgType>(qStatus)
    );
  }

  void SmChoiceActiveComponentBase ::
    smChoiceInputPairU16U32_sendSignalFinish(Fw::SerializeBufferBase& buffer)
  {
    // Send message
    Os::Queue::BlockingType _block = Os::Queue::NONBLOCKING;
    Os::Queue::Status qStatus = this->m_queue.send(buffer, 3, _block);

    if (qStatus == Os::Queue::Status::FULL) {
      this->incNumMsgDropped();
      return;
    }

    FW_ASSERT(
      qStatus == Os::Queue::OP_OK,
      static_cast<FwAssertArgType>(qStatus)
    );
  }

  void SmChoiceActiveComponentBase ::
    smChoiceSequence_sendSignalFinish(Fw::SerializeBufferBase& buffer)
  {
    // Send message
    Os::Queue::BlockingType _block = Os::Queue::NONBLOCKING;
    Os::Queue::Status qStatus = this->m_queue.send(buffer, 0, _block);

    FW_ASSERT(
      qStatus == Os::Queue::OP_OK,
      static_cast<FwAssertArgType>(qStatus)
    );
  }

  void SmChoiceActiveComponentBase ::
    smChoiceSequenceU32_sendSignalFinish(Fw::SerializeBufferBase& buffer)
  {
    // Send message
    Os::Queue::BlockingType _block = Os::Queue::NONBLOCKING;
    Os::Queue::Status qStatus = this->m_queue.send(buffer, 0, _block);

    FW_ASSERT(
      qStatus == Os::Queue::OP_OK,
      static_cast<FwAssertArgType>(qStatus)
    );
  }

  // ----------------------------------------------------------------------
  // Helper functions for state machine dispatch
  // ----------------------------------------------------------------------

  void SmChoiceActiveComponentBase ::
    smDispatch(Fw::SerializeBufferBase& buffer)
  {
    // Deserialize the state machine ID and signal
    FwEnumStoreType storedSmId;
    FwEnumStoreType storedSignal;
    SmChoiceActiveComponentBase::deserializeSmIdAndSignal(buffer, storedSmId, storedSignal);

    // Select the target state machine instance
    const SmId smId = static_cast<SmId>(storedSmId);
    switch (smId) {
      case SmId::basic: {
        const FppTest_SmChoiceActive_Basic::Signal signal = static_cast<FppTest_SmChoiceActive_Basic::Signal>(storedSignal);
        this->FppTest_SmChoiceActive_Basic_smDispatch(buffer, this->m_stateMachine_basic, signal);
        break;
      }
      case SmId::smChoiceBasic: {
        const FppTest_SmChoice_Basic::Signal signal = static_cast<FppTest_SmChoice_Basic::Signal>(storedSignal);
        this->FppTest_SmChoice_Basic_smDispatch(buffer, this->m_stateMachine_smChoiceBasic, signal);
        break;
      }
      case SmId::smChoiceBasicU32: {
        const FppTest_SmChoice_BasicU32::Signal signal = static_cast<FppTest_SmChoice_BasicU32::Signal>(storedSignal);
        this->FppTest_SmChoice_BasicU32_smDispatch(buffer, this->m_stateMachine_smChoiceBasicU32, signal);
        break;
      }
      case SmId::smChoiceChoiceToChoice: {
        const FppTest_SmChoice_ChoiceToChoice::Signal signal = static_cast<FppTest_SmChoice_ChoiceToChoice::Signal>(storedSignal);
        this->FppTest_SmChoice_ChoiceToChoice_smDispatch(buffer, this->m_stateMachine_smChoiceChoiceToChoice, signal);
        break;
      }
      case SmId::smChoiceChoiceToState: {
        const FppTest_SmChoice_ChoiceToState::Signal signal = static_cast<FppTest_SmChoice_ChoiceToState::Signal>(storedSignal);
        this->FppTest_SmChoice_ChoiceToState_smDispatch(buffer, this->m_stateMachine_smChoiceChoiceToState, signal);
        break;
      }
      case SmId::smChoiceInputPairU16U32: {
        const FppTest_SmChoice_InputPairU16U32::Signal signal = static_cast<FppTest_SmChoice_InputPairU16U32::Signal>(storedSignal);
        this->FppTest_SmChoice_InputPairU16U32_smDispatch(buffer, this->m_stateMachine_smChoiceInputPairU16U32, signal);
        break;
      }
      case SmId::smChoiceSequence: {
        const FppTest_SmChoice_Sequence::Signal signal = static_cast<FppTest_SmChoice_Sequence::Signal>(storedSignal);
        this->FppTest_SmChoice_Sequence_smDispatch(buffer, this->m_stateMachine_smChoiceSequence, signal);
        break;
      }
      case SmId::smChoiceSequenceU32: {
        const FppTest_SmChoice_SequenceU32::Signal signal = static_cast<FppTest_SmChoice_SequenceU32::Signal>(storedSignal);
        this->FppTest_SmChoice_SequenceU32_smDispatch(buffer, this->m_stateMachine_smChoiceSequenceU32, signal);
        break;
      }
      default:
        FW_ASSERT(0, static_cast<FwAssertArgType>(smId));
        break;
    }
  }

  void SmChoiceActiveComponentBase ::
    deserializeSmIdAndSignal(
        Fw::SerializeBufferBase& buffer,
        FwEnumStoreType& smId,
        FwEnumStoreType& signal
    )
  {
    // Move deserialization beyond the message type and port number
    Fw::SerializeStatus status =
      buffer.moveDeserToOffset(ComponentIpcSerializableBuffer::DATA_OFFSET);
    FW_ASSERT(status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(status));

    // Deserialize the state machine ID
    status = buffer.deserialize(smId);
    FW_ASSERT(status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(status));

    // Deserialize the signal
    status = buffer.deserialize(signal);
    FW_ASSERT(status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(status));
  }

  void SmChoiceActiveComponentBase ::
    FppTest_SmChoice_Basic_smDispatch(
        Fw::SerializeBufferBase& buffer,
        FppTest_SmChoice_Basic& sm,
        FppTest_SmChoice_Basic::Signal signal
    )
  {
    switch (signal) {
      case FppTest_SmChoice_Basic::Signal::s: {
        // Assert no data left in buffer
        FW_ASSERT(buffer.getBuffLeft() == 0, static_cast<FwAssertArgType>(buffer.getBuffLeft()));
        // Call the sendSignal function for sm and s
        sm.sendSignal_s();
        break;
      }
      default:
        FW_ASSERT(0, static_cast<FwAssertArgType>(signal));
        break;
    }
  }

  void SmChoiceActiveComponentBase ::
    FppTest_SmChoice_BasicU32_smDispatch(
        Fw::SerializeBufferBase& buffer,
        FppTest_SmChoice_BasicU32& sm,
        FppTest_SmChoice_BasicU32::Signal signal
    )
  {
    switch (signal) {
      case FppTest_SmChoice_BasicU32::Signal::s: {
        // Deserialize the data
        U32 value;
        const Fw::SerializeStatus status = buffer.deserialize(value);
        FW_ASSERT(status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(status));
        // Assert no data left in buffer
        FW_ASSERT(buffer.getBuffLeft() == 0, static_cast<FwAssertArgType>(buffer.getBuffLeft()));
        // Call the sendSignal function for sm and s
        sm.sendSignal_s(value);
        break;
      }
      default:
        FW_ASSERT(0, static_cast<FwAssertArgType>(signal));
        break;
    }
  }

  void SmChoiceActiveComponentBase ::
    FppTest_SmChoice_ChoiceToChoice_smDispatch(
        Fw::SerializeBufferBase& buffer,
        FppTest_SmChoice_ChoiceToChoice& sm,
        FppTest_SmChoice_ChoiceToChoice::Signal signal
    )
  {
    switch (signal) {
      case FppTest_SmChoice_ChoiceToChoice::Signal::s: {
        // Assert no data left in buffer
        FW_ASSERT(buffer.getBuffLeft() == 0, static_cast<FwAssertArgType>(buffer.getBuffLeft()));
        // Call the sendSignal function for sm and s
        sm.sendSignal_s();
        break;
      }
      default:
        FW_ASSERT(0, static_cast<FwAssertArgType>(signal));
        break;
    }
  }

  void SmChoiceActiveComponentBase ::
    FppTest_SmChoice_ChoiceToState_smDispatch(
        Fw::SerializeBufferBase& buffer,
        FppTest_SmChoice_ChoiceToState& sm,
        FppTest_SmChoice_ChoiceToState::Signal signal
    )
  {
    switch (signal) {
      case FppTest_SmChoice_ChoiceToState::Signal::s: {
        // Assert no data left in buffer
        FW_ASSERT(buffer.getBuffLeft() == 0, static_cast<FwAssertArgType>(buffer.getBuffLeft()));
        // Call the sendSignal function for sm and s
        sm.sendSignal_s();
        break;
      }
      default:
        FW_ASSERT(0, static_cast<FwAssertArgType>(signal));
        break;
    }
  }

  void SmChoiceActiveComponentBase ::
    FppTest_SmChoice_InputPairU16U32_smDispatch(
        Fw::SerializeBufferBase& buffer,
        FppTest_SmChoice_InputPairU16U32& sm,
        FppTest_SmChoice_InputPairU16U32::Signal signal
    )
  {
    switch (signal) {
      case FppTest_SmChoice_InputPairU16U32::Signal::s1: {
        // Deserialize the data
        U16 value;
        const Fw::SerializeStatus status = buffer.deserialize(value);
        FW_ASSERT(status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(status));
        // Assert no data left in buffer
        FW_ASSERT(buffer.getBuffLeft() == 0, static_cast<FwAssertArgType>(buffer.getBuffLeft()));
        // Call the sendSignal function for sm and s1
        sm.sendSignal_s1(value);
        break;
      }
      case FppTest_SmChoice_InputPairU16U32::Signal::s2: {
        // Deserialize the data
        U32 value;
        const Fw::SerializeStatus status = buffer.deserialize(value);
        FW_ASSERT(status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(status));
        // Assert no data left in buffer
        FW_ASSERT(buffer.getBuffLeft() == 0, static_cast<FwAssertArgType>(buffer.getBuffLeft()));
        // Call the sendSignal function for sm and s2
        sm.sendSignal_s2(value);
        break;
      }
      default:
        FW_ASSERT(0, static_cast<FwAssertArgType>(signal));
        break;
    }
  }

  void SmChoiceActiveComponentBase ::
    FppTest_SmChoice_Sequence_smDispatch(
        Fw::SerializeBufferBase& buffer,
        FppTest_SmChoice_Sequence& sm,
        FppTest_SmChoice_Sequence::Signal signal
    )
  {
    switch (signal) {
      case FppTest_SmChoice_Sequence::Signal::s: {
        // Assert no data left in buffer
        FW_ASSERT(buffer.getBuffLeft() == 0, static_cast<FwAssertArgType>(buffer.getBuffLeft()));
        // Call the sendSignal function for sm and s
        sm.sendSignal_s();
        break;
      }
      default:
        FW_ASSERT(0, static_cast<FwAssertArgType>(signal));
        break;
    }
  }

  void SmChoiceActiveComponentBase ::
    FppTest_SmChoice_SequenceU32_smDispatch(
        Fw::SerializeBufferBase& buffer,
        FppTest_SmChoice_SequenceU32& sm,
        FppTest_SmChoice_SequenceU32::Signal signal
    )
  {
    switch (signal) {
      case FppTest_SmChoice_SequenceU32::Signal::s: {
        // Deserialize the data
        U32 value;
        const Fw::SerializeStatus status = buffer.deserialize(value);
        FW_ASSERT(status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(status));
        // Assert no data left in buffer
        FW_ASSERT(buffer.getBuffLeft() == 0, static_cast<FwAssertArgType>(buffer.getBuffLeft()));
        // Call the sendSignal function for sm and s
        sm.sendSignal_s(value);
        break;
      }
      default:
        FW_ASSERT(0, static_cast<FwAssertArgType>(signal));
        break;
    }
  }

  void SmChoiceActiveComponentBase ::
    FppTest_SmChoiceActive_Basic_smDispatch(
        Fw::SerializeBufferBase& buffer,
        FppTest_SmChoiceActive_Basic& sm,
        FppTest_SmChoiceActive_Basic::Signal signal
    )
  {
    switch (signal) {
      case FppTest_SmChoiceActive_Basic::Signal::s: {
        // Assert no data left in buffer
        FW_ASSERT(buffer.getBuffLeft() == 0, static_cast<FwAssertArgType>(buffer.getBuffLeft()));
        // Call the sendSignal function for sm and s
        sm.sendSignal_s();
        break;
      }
      default:
        FW_ASSERT(0, static_cast<FwAssertArgType>(signal));
        break;
    }
  }

}