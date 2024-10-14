// ======================================================================
// \title  SmStateQueuedComponentAc.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for SmStateQueued component base class
// ======================================================================

#include "Fw/Types/Assert.hpp"
#include "Fw/Types/ExternalString.hpp"
#if FW_ENABLE_TEXT_LOGGING
#include "Fw/Types/String.hpp"
#endif
#include "base/SmStateQueuedComponentAc.hpp"

namespace FppTest {

  namespace {

    // Constant definitions for the state machine signal buffer
    namespace SmSignalBuffer {

      // Union for computing the max size of a signal type
      union SignalTypeUnion {
        BYTE size_of_FppTest_SmHarness_TestAbsType[FppTest::SmHarness::TestAbsType::SERIALIZED_SIZE];
        BYTE size_of_FppTest_SmHarness_TestArray[FppTest::SmHarness::TestArray::SERIALIZED_SIZE];
        BYTE size_of_FppTest_SmHarness_TestEnum[FppTest::SmHarness::TestEnum::SERIALIZED_SIZE];
        BYTE size_of_string[Fw::StringBase::STATIC_SERIALIZED_SIZE(80)];
      };

      // The serialized size
      static constexpr FwSizeType SERIALIZED_SIZE =
        2 * sizeof(FwEnumStoreType) +
        sizeof(SignalTypeUnion);

    }

    enum MsgTypeEnum {
      SMSTATEQUEUED_COMPONENT_EXIT = Fw::ActiveComponentBase::ACTIVE_COMPONENT_EXIT,
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

  SmStateQueuedComponentBase::FppTest_SmState_Basic ::
    FppTest_SmState_Basic(SmStateQueuedComponentBase& component) :
      m_component(component)
  {

  }

  void SmStateQueuedComponentBase::FppTest_SmState_Basic ::
    init(SmStateQueuedComponentBase::SmId smId)
  {
    this->initBase(static_cast<FwEnumStoreType>(smId));
  }

  SmStateQueuedComponentBase::SmId SmStateQueuedComponentBase::FppTest_SmState_Basic ::
    getId() const
  {
    return static_cast<SmStateQueuedComponentBase::SmId>(this->m_id);
  }

  void SmStateQueuedComponentBase::FppTest_SmState_Basic ::
    action_a(Signal signal)
  {
    this->m_component.FppTest_SmState_Basic_action_a(this->getId(), signal);
  }

  SmStateQueuedComponentBase::FppTest_SmState_BasicGuard ::
    FppTest_SmState_BasicGuard(SmStateQueuedComponentBase& component) :
      m_component(component)
  {

  }

  void SmStateQueuedComponentBase::FppTest_SmState_BasicGuard ::
    init(SmStateQueuedComponentBase::SmId smId)
  {
    this->initBase(static_cast<FwEnumStoreType>(smId));
  }

  SmStateQueuedComponentBase::SmId SmStateQueuedComponentBase::FppTest_SmState_BasicGuard ::
    getId() const
  {
    return static_cast<SmStateQueuedComponentBase::SmId>(this->m_id);
  }

  void SmStateQueuedComponentBase::FppTest_SmState_BasicGuard ::
    action_a(Signal signal)
  {
    this->m_component.FppTest_SmState_BasicGuard_action_a(this->getId(), signal);
  }

  bool SmStateQueuedComponentBase::FppTest_SmState_BasicGuard ::
    guard_g(Signal signal) const
  {
    return this->m_component.FppTest_SmState_BasicGuard_guard_g(this->getId(), signal);
  }

  SmStateQueuedComponentBase::FppTest_SmState_BasicGuardString ::
    FppTest_SmState_BasicGuardString(SmStateQueuedComponentBase& component) :
      m_component(component)
  {

  }

  void SmStateQueuedComponentBase::FppTest_SmState_BasicGuardString ::
    init(SmStateQueuedComponentBase::SmId smId)
  {
    this->initBase(static_cast<FwEnumStoreType>(smId));
  }

  SmStateQueuedComponentBase::SmId SmStateQueuedComponentBase::FppTest_SmState_BasicGuardString ::
    getId() const
  {
    return static_cast<SmStateQueuedComponentBase::SmId>(this->m_id);
  }

  void SmStateQueuedComponentBase::FppTest_SmState_BasicGuardString ::
    action_a(
        Signal signal,
        const Fw::StringBase& value
    )
  {
    this->m_component.FppTest_SmState_BasicGuardString_action_a(this->getId(), signal, value);
  }

  bool SmStateQueuedComponentBase::FppTest_SmState_BasicGuardString ::
    guard_g(
        Signal signal,
        const Fw::StringBase& value
    ) const
  {
    return this->m_component.FppTest_SmState_BasicGuardString_guard_g(this->getId(), signal, value);
  }

  SmStateQueuedComponentBase::FppTest_SmState_BasicGuardTestAbsType ::
    FppTest_SmState_BasicGuardTestAbsType(SmStateQueuedComponentBase& component) :
      m_component(component)
  {

  }

  void SmStateQueuedComponentBase::FppTest_SmState_BasicGuardTestAbsType ::
    init(SmStateQueuedComponentBase::SmId smId)
  {
    this->initBase(static_cast<FwEnumStoreType>(smId));
  }

  SmStateQueuedComponentBase::SmId SmStateQueuedComponentBase::FppTest_SmState_BasicGuardTestAbsType ::
    getId() const
  {
    return static_cast<SmStateQueuedComponentBase::SmId>(this->m_id);
  }

  void SmStateQueuedComponentBase::FppTest_SmState_BasicGuardTestAbsType ::
    action_a(
        Signal signal,
        const FppTest::SmHarness::TestAbsType& value
    )
  {
    this->m_component.FppTest_SmState_BasicGuardTestAbsType_action_a(this->getId(), signal, value);
  }

  bool SmStateQueuedComponentBase::FppTest_SmState_BasicGuardTestAbsType ::
    guard_g(
        Signal signal,
        const FppTest::SmHarness::TestAbsType& value
    ) const
  {
    return this->m_component.FppTest_SmState_BasicGuardTestAbsType_guard_g(this->getId(), signal, value);
  }

  SmStateQueuedComponentBase::FppTest_SmState_BasicGuardTestArray ::
    FppTest_SmState_BasicGuardTestArray(SmStateQueuedComponentBase& component) :
      m_component(component)
  {

  }

  void SmStateQueuedComponentBase::FppTest_SmState_BasicGuardTestArray ::
    init(SmStateQueuedComponentBase::SmId smId)
  {
    this->initBase(static_cast<FwEnumStoreType>(smId));
  }

  SmStateQueuedComponentBase::SmId SmStateQueuedComponentBase::FppTest_SmState_BasicGuardTestArray ::
    getId() const
  {
    return static_cast<SmStateQueuedComponentBase::SmId>(this->m_id);
  }

  void SmStateQueuedComponentBase::FppTest_SmState_BasicGuardTestArray ::
    action_a(
        Signal signal,
        const FppTest::SmHarness::TestArray& value
    )
  {
    this->m_component.FppTest_SmState_BasicGuardTestArray_action_a(this->getId(), signal, value);
  }

  bool SmStateQueuedComponentBase::FppTest_SmState_BasicGuardTestArray ::
    guard_g(
        Signal signal,
        const FppTest::SmHarness::TestArray& value
    ) const
  {
    return this->m_component.FppTest_SmState_BasicGuardTestArray_guard_g(this->getId(), signal, value);
  }

  SmStateQueuedComponentBase::FppTest_SmState_BasicGuardTestEnum ::
    FppTest_SmState_BasicGuardTestEnum(SmStateQueuedComponentBase& component) :
      m_component(component)
  {

  }

  void SmStateQueuedComponentBase::FppTest_SmState_BasicGuardTestEnum ::
    init(SmStateQueuedComponentBase::SmId smId)
  {
    this->initBase(static_cast<FwEnumStoreType>(smId));
  }

  SmStateQueuedComponentBase::SmId SmStateQueuedComponentBase::FppTest_SmState_BasicGuardTestEnum ::
    getId() const
  {
    return static_cast<SmStateQueuedComponentBase::SmId>(this->m_id);
  }

  void SmStateQueuedComponentBase::FppTest_SmState_BasicGuardTestEnum ::
    action_a(
        Signal signal,
        const FppTest::SmHarness::TestEnum& value
    )
  {
    this->m_component.FppTest_SmState_BasicGuardTestEnum_action_a(this->getId(), signal, value);
  }

  bool SmStateQueuedComponentBase::FppTest_SmState_BasicGuardTestEnum ::
    guard_g(
        Signal signal,
        const FppTest::SmHarness::TestEnum& value
    ) const
  {
    return this->m_component.FppTest_SmState_BasicGuardTestEnum_guard_g(this->getId(), signal, value);
  }

  SmStateQueuedComponentBase::FppTest_SmStateQueued_Basic ::
    FppTest_SmStateQueued_Basic(SmStateQueuedComponentBase& component) :
      m_component(component)
  {

  }

  void SmStateQueuedComponentBase::FppTest_SmStateQueued_Basic ::
    init(SmStateQueuedComponentBase::SmId smId)
  {
    this->initBase(static_cast<FwEnumStoreType>(smId));
  }

  SmStateQueuedComponentBase::SmId SmStateQueuedComponentBase::FppTest_SmStateQueued_Basic ::
    getId() const
  {
    return static_cast<SmStateQueuedComponentBase::SmId>(this->m_id);
  }

  void SmStateQueuedComponentBase::FppTest_SmStateQueued_Basic ::
    action_a(Signal signal)
  {
    this->m_component.FppTest_SmStateQueued_Basic_action_a(this->getId(), signal);
  }

  // ----------------------------------------------------------------------
  // Component initialization
  // ----------------------------------------------------------------------

  void SmStateQueuedComponentBase ::
    init(
        FwSizeType queueDepth,
        FwEnumStoreType instance
    )
  {
    // Initialize base class
    Fw::QueuedComponentBase::init(instance);

    this->m_stateMachine_basic.init(SmId::basic);
    this->m_stateMachine_smStateBasic.init(SmId::smStateBasic);
    this->m_stateMachine_smStateBasicGuard.init(SmId::smStateBasicGuard);
    this->m_stateMachine_smStateBasicGuardString.init(SmId::smStateBasicGuardString);
    this->m_stateMachine_smStateBasicGuardTestAbsType.init(SmId::smStateBasicGuardTestAbsType);
    this->m_stateMachine_smStateBasicGuardTestArray.init(SmId::smStateBasicGuardTestArray);
    this->m_stateMachine_smStateBasicGuardTestEnum.init(SmId::smStateBasicGuardTestEnum);

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

  SmStateQueuedComponentBase ::
    SmStateQueuedComponentBase(const char* compName) :
      Fw::QueuedComponentBase(compName),
      m_stateMachine_basic(*this),
      m_stateMachine_smStateBasic(*this),
      m_stateMachine_smStateBasicGuard(*this),
      m_stateMachine_smStateBasicGuardString(*this),
      m_stateMachine_smStateBasicGuardTestAbsType(*this),
      m_stateMachine_smStateBasicGuardTestArray(*this),
      m_stateMachine_smStateBasicGuardTestEnum(*this)
  {

  }

  SmStateQueuedComponentBase ::
    ~SmStateQueuedComponentBase()
  {

  }

  // ----------------------------------------------------------------------
  // State getter functions
  // ----------------------------------------------------------------------

  SmStateQueuedComponentBase::FppTest_SmStateQueued_Basic::State SmStateQueuedComponentBase ::
    basic_getState() const
  {
    return this->m_stateMachine_basic.getState();
  }

  SmStateQueuedComponentBase::FppTest_SmState_Basic::State SmStateQueuedComponentBase ::
    smStateBasic_getState() const
  {
    return this->m_stateMachine_smStateBasic.getState();
  }

  SmStateQueuedComponentBase::FppTest_SmState_BasicGuard::State SmStateQueuedComponentBase ::
    smStateBasicGuard_getState() const
  {
    return this->m_stateMachine_smStateBasicGuard.getState();
  }

  SmStateQueuedComponentBase::FppTest_SmState_BasicGuardString::State SmStateQueuedComponentBase ::
    smStateBasicGuardString_getState() const
  {
    return this->m_stateMachine_smStateBasicGuardString.getState();
  }

  SmStateQueuedComponentBase::FppTest_SmState_BasicGuardTestAbsType::State SmStateQueuedComponentBase ::
    smStateBasicGuardTestAbsType_getState() const
  {
    return this->m_stateMachine_smStateBasicGuardTestAbsType.getState();
  }

  SmStateQueuedComponentBase::FppTest_SmState_BasicGuardTestArray::State SmStateQueuedComponentBase ::
    smStateBasicGuardTestArray_getState() const
  {
    return this->m_stateMachine_smStateBasicGuardTestArray.getState();
  }

  SmStateQueuedComponentBase::FppTest_SmState_BasicGuardTestEnum::State SmStateQueuedComponentBase ::
    smStateBasicGuardTestEnum_getState() const
  {
    return this->m_stateMachine_smStateBasicGuardTestEnum.getState();
  }

  // ----------------------------------------------------------------------
  // Signal send functions
  // ----------------------------------------------------------------------

  void SmStateQueuedComponentBase ::
    basic_sendSignal_s()
  {
    ComponentIpcSerializableBuffer buffer;
    // Serialize the message type, port number, state ID, and signal
    this->sendSignalStart(SmId::basic, static_cast<FwEnumStoreType>(FppTest_SmStateQueued_Basic::Signal::s), buffer);
    // Send the message and handle overflow
    this->basic_sendSignalFinish(buffer);
  }

  void SmStateQueuedComponentBase ::
    smStateBasic_sendSignal_s()
  {
    ComponentIpcSerializableBuffer buffer;
    // Serialize the message type, port number, state ID, and signal
    this->sendSignalStart(SmId::smStateBasic, static_cast<FwEnumStoreType>(FppTest_SmState_Basic::Signal::s), buffer);
    // Send the message and handle overflow
    this->smStateBasic_sendSignalFinish(buffer);
  }

  void SmStateQueuedComponentBase ::
    smStateBasicGuard_sendSignal_s()
  {
    ComponentIpcSerializableBuffer buffer;
    // Serialize the message type, port number, state ID, and signal
    this->sendSignalStart(SmId::smStateBasicGuard, static_cast<FwEnumStoreType>(FppTest_SmState_BasicGuard::Signal::s), buffer);
    // Send the message and handle overflow
    this->smStateBasicGuard_sendSignalFinish(buffer);
  }

  void SmStateQueuedComponentBase ::
    smStateBasicGuardString_sendSignal_s(const Fw::StringBase& value)
  {
    ComponentIpcSerializableBuffer buffer;
    // Serialize the message type, port number, state ID, and signal
    this->sendSignalStart(SmId::smStateBasicGuardString, static_cast<FwEnumStoreType>(FppTest_SmState_BasicGuardString::Signal::s), buffer);
    // Serialize the signal data
    const Fw::SerializeStatus status = value.serialize(buffer, 80);
    FW_ASSERT(status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(status));
    // Send the message and handle overflow
    this->smStateBasicGuardString_sendSignalFinish(buffer);
  }

  void SmStateQueuedComponentBase ::
    smStateBasicGuardTestAbsType_sendSignal_s(const FppTest::SmHarness::TestAbsType& value)
  {
    ComponentIpcSerializableBuffer buffer;
    // Serialize the message type, port number, state ID, and signal
    this->sendSignalStart(SmId::smStateBasicGuardTestAbsType, static_cast<FwEnumStoreType>(FppTest_SmState_BasicGuardTestAbsType::Signal::s), buffer);
    // Serialize the signal data
    const Fw::SerializeStatus status = buffer.serialize(value);
    FW_ASSERT(status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(status));
    // Send the message and handle overflow
    this->smStateBasicGuardTestAbsType_sendSignalFinish(buffer);
  }

  void SmStateQueuedComponentBase ::
    smStateBasicGuardTestArray_sendSignal_s(const FppTest::SmHarness::TestArray& value)
  {
    ComponentIpcSerializableBuffer buffer;
    // Serialize the message type, port number, state ID, and signal
    this->sendSignalStart(SmId::smStateBasicGuardTestArray, static_cast<FwEnumStoreType>(FppTest_SmState_BasicGuardTestArray::Signal::s), buffer);
    // Serialize the signal data
    const Fw::SerializeStatus status = buffer.serialize(value);
    FW_ASSERT(status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(status));
    // Send the message and handle overflow
    this->smStateBasicGuardTestArray_sendSignalFinish(buffer);
  }

  void SmStateQueuedComponentBase ::
    smStateBasicGuardTestEnum_sendSignal_s(const FppTest::SmHarness::TestEnum& value)
  {
    ComponentIpcSerializableBuffer buffer;
    // Serialize the message type, port number, state ID, and signal
    this->sendSignalStart(SmId::smStateBasicGuardTestEnum, static_cast<FwEnumStoreType>(FppTest_SmState_BasicGuardTestEnum::Signal::s), buffer);
    // Serialize the signal data
    const Fw::SerializeStatus status = buffer.serialize(value);
    FW_ASSERT(status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(status));
    // Send the message and handle overflow
    this->smStateBasicGuardTestEnum_sendSignalFinish(buffer);
  }

  // ----------------------------------------------------------------------
  // Message dispatch functions
  // ----------------------------------------------------------------------

  Fw::QueuedComponentBase::MsgDispatchStatus SmStateQueuedComponentBase ::
    doDispatch()
  {
    ComponentIpcSerializableBuffer msg;
    FwQueuePriorityType priority = 0;

    Os::Queue::Status msgStatus = this->m_queue.receive(
      msg,
      Os::Queue::NONBLOCKING,
      priority
    );
    if (Os::Queue::Status::EMPTY == msgStatus) {
      return Fw::QueuedComponentBase::MSG_DISPATCH_EMPTY;
    }
    else {
      FW_ASSERT(
        msgStatus == Os::Queue::OP_OK,
        static_cast<FwAssertArgType>(msgStatus)
      );
    }

    // Reset to beginning of buffer
    msg.resetDeser();

    FwEnumStoreType desMsg = 0;
    Fw::SerializeStatus deserStatus = msg.deserialize(desMsg);
    FW_ASSERT(
      deserStatus == Fw::FW_SERIALIZE_OK,
      static_cast<FwAssertArgType>(deserStatus)
    );

    MsgTypeEnum msgType = static_cast<MsgTypeEnum>(desMsg);

    if (msgType == SMSTATEQUEUED_COMPONENT_EXIT) {
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

  void SmStateQueuedComponentBase ::
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

  void SmStateQueuedComponentBase ::
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

  void SmStateQueuedComponentBase ::
    smStateBasic_sendSignalFinish(Fw::SerializeBufferBase& buffer)
  {
    // Send message
    Os::Queue::BlockingType _block = Os::Queue::NONBLOCKING;
    Os::Queue::Status qStatus = this->m_queue.send(buffer, 1, _block);

    FW_ASSERT(
      qStatus == Os::Queue::OP_OK,
      static_cast<FwAssertArgType>(qStatus)
    );
  }

  void SmStateQueuedComponentBase ::
    smStateBasicGuard_sendSignalFinish(Fw::SerializeBufferBase& buffer)
  {
    // Send message
    Os::Queue::BlockingType _block = Os::Queue::BLOCKING;
    Os::Queue::Status qStatus = this->m_queue.send(buffer, 2, _block);

    FW_ASSERT(
      qStatus == Os::Queue::OP_OK,
      static_cast<FwAssertArgType>(qStatus)
    );
  }

  void SmStateQueuedComponentBase ::
    smStateBasicGuardString_sendSignalFinish(Fw::SerializeBufferBase& buffer)
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

  void SmStateQueuedComponentBase ::
    smStateBasicGuardTestAbsType_sendSignalFinish(Fw::SerializeBufferBase& buffer)
  {
    // Send message
    Os::Queue::BlockingType _block = Os::Queue::NONBLOCKING;
    Os::Queue::Status qStatus = this->m_queue.send(buffer, 4, _block);

    if (qStatus == Os::Queue::Status::FULL) {

      // Deserialize the state machine ID and signal
      FwEnumStoreType smId;
      FwEnumStoreType signal;
      SmStateQueuedComponentBase::deserializeSmIdAndSignal(buffer, smId, signal);

      // Call the overflow hook
      this->smStateBasicGuardTestAbsType_stateMachineOverflowHook(static_cast<SmId>(smId), signal, buffer);

      // Continue execution
      return;

    }

    FW_ASSERT(
      qStatus == Os::Queue::OP_OK,
      static_cast<FwAssertArgType>(qStatus)
    );
  }

  void SmStateQueuedComponentBase ::
    smStateBasicGuardTestArray_sendSignalFinish(Fw::SerializeBufferBase& buffer)
  {
    // Send message
    Os::Queue::BlockingType _block = Os::Queue::NONBLOCKING;
    Os::Queue::Status qStatus = this->m_queue.send(buffer, 0, _block);

    FW_ASSERT(
      qStatus == Os::Queue::OP_OK,
      static_cast<FwAssertArgType>(qStatus)
    );
  }

  void SmStateQueuedComponentBase ::
    smStateBasicGuardTestEnum_sendSignalFinish(Fw::SerializeBufferBase& buffer)
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

  void SmStateQueuedComponentBase ::
    smDispatch(Fw::SerializeBufferBase& buffer)
  {
    // Deserialize the state machine ID and signal
    FwEnumStoreType storedSmId;
    FwEnumStoreType storedSignal;
    SmStateQueuedComponentBase::deserializeSmIdAndSignal(buffer, storedSmId, storedSignal);

    // Select the target state machine instance
    const SmId smId = static_cast<SmId>(storedSmId);
    switch (smId) {
      case SmId::basic: {
        const FppTest_SmStateQueued_Basic::Signal signal = static_cast<FppTest_SmStateQueued_Basic::Signal>(storedSignal);
        this->FppTest_SmStateQueued_Basic_smDispatch(buffer, this->m_stateMachine_basic, signal);
        break;
      }
      case SmId::smStateBasic: {
        const FppTest_SmState_Basic::Signal signal = static_cast<FppTest_SmState_Basic::Signal>(storedSignal);
        this->FppTest_SmState_Basic_smDispatch(buffer, this->m_stateMachine_smStateBasic, signal);
        break;
      }
      case SmId::smStateBasicGuard: {
        const FppTest_SmState_BasicGuard::Signal signal = static_cast<FppTest_SmState_BasicGuard::Signal>(storedSignal);
        this->FppTest_SmState_BasicGuard_smDispatch(buffer, this->m_stateMachine_smStateBasicGuard, signal);
        break;
      }
      case SmId::smStateBasicGuardString: {
        const FppTest_SmState_BasicGuardString::Signal signal = static_cast<FppTest_SmState_BasicGuardString::Signal>(storedSignal);
        this->FppTest_SmState_BasicGuardString_smDispatch(buffer, this->m_stateMachine_smStateBasicGuardString, signal);
        break;
      }
      case SmId::smStateBasicGuardTestAbsType: {
        const FppTest_SmState_BasicGuardTestAbsType::Signal signal = static_cast<FppTest_SmState_BasicGuardTestAbsType::Signal>(storedSignal);
        this->FppTest_SmState_BasicGuardTestAbsType_smDispatch(buffer, this->m_stateMachine_smStateBasicGuardTestAbsType, signal);
        break;
      }
      case SmId::smStateBasicGuardTestArray: {
        const FppTest_SmState_BasicGuardTestArray::Signal signal = static_cast<FppTest_SmState_BasicGuardTestArray::Signal>(storedSignal);
        this->FppTest_SmState_BasicGuardTestArray_smDispatch(buffer, this->m_stateMachine_smStateBasicGuardTestArray, signal);
        break;
      }
      case SmId::smStateBasicGuardTestEnum: {
        const FppTest_SmState_BasicGuardTestEnum::Signal signal = static_cast<FppTest_SmState_BasicGuardTestEnum::Signal>(storedSignal);
        this->FppTest_SmState_BasicGuardTestEnum_smDispatch(buffer, this->m_stateMachine_smStateBasicGuardTestEnum, signal);
        break;
      }
      default:
        FW_ASSERT(0, static_cast<FwAssertArgType>(smId));
        break;
    }
  }

  void SmStateQueuedComponentBase ::
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

  void SmStateQueuedComponentBase ::
    FppTest_SmState_Basic_smDispatch(
        Fw::SerializeBufferBase& buffer,
        FppTest_SmState_Basic& sm,
        FppTest_SmState_Basic::Signal signal
    )
  {
    switch (signal) {
      case FppTest_SmState_Basic::Signal::s: {
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

  void SmStateQueuedComponentBase ::
    FppTest_SmState_BasicGuard_smDispatch(
        Fw::SerializeBufferBase& buffer,
        FppTest_SmState_BasicGuard& sm,
        FppTest_SmState_BasicGuard::Signal signal
    )
  {
    switch (signal) {
      case FppTest_SmState_BasicGuard::Signal::s: {
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

  void SmStateQueuedComponentBase ::
    FppTest_SmState_BasicGuardString_smDispatch(
        Fw::SerializeBufferBase& buffer,
        FppTest_SmState_BasicGuardString& sm,
        FppTest_SmState_BasicGuardString::Signal signal
    )
  {
    switch (signal) {
      case FppTest_SmState_BasicGuardString::Signal::s: {
        // Deserialize the data
        char __fprime_ac_value_buffer[Fw::StringBase::BUFFER_SIZE(80)];
        Fw::ExternalString value(__fprime_ac_value_buffer, sizeof __fprime_ac_value_buffer);
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

  void SmStateQueuedComponentBase ::
    FppTest_SmState_BasicGuardTestAbsType_smDispatch(
        Fw::SerializeBufferBase& buffer,
        FppTest_SmState_BasicGuardTestAbsType& sm,
        FppTest_SmState_BasicGuardTestAbsType::Signal signal
    )
  {
    switch (signal) {
      case FppTest_SmState_BasicGuardTestAbsType::Signal::s: {
        // Deserialize the data
        FppTest::SmHarness::TestAbsType value;
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

  void SmStateQueuedComponentBase ::
    FppTest_SmState_BasicGuardTestArray_smDispatch(
        Fw::SerializeBufferBase& buffer,
        FppTest_SmState_BasicGuardTestArray& sm,
        FppTest_SmState_BasicGuardTestArray::Signal signal
    )
  {
    switch (signal) {
      case FppTest_SmState_BasicGuardTestArray::Signal::s: {
        // Deserialize the data
        FppTest::SmHarness::TestArray value;
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

  void SmStateQueuedComponentBase ::
    FppTest_SmState_BasicGuardTestEnum_smDispatch(
        Fw::SerializeBufferBase& buffer,
        FppTest_SmState_BasicGuardTestEnum& sm,
        FppTest_SmState_BasicGuardTestEnum::Signal signal
    )
  {
    switch (signal) {
      case FppTest_SmState_BasicGuardTestEnum::Signal::s: {
        // Deserialize the data
        FppTest::SmHarness::TestEnum value;
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

  void SmStateQueuedComponentBase ::
    FppTest_SmStateQueued_Basic_smDispatch(
        Fw::SerializeBufferBase& buffer,
        FppTest_SmStateQueued_Basic& sm,
        FppTest_SmStateQueued_Basic::Signal signal
    )
  {
    switch (signal) {
      case FppTest_SmStateQueued_Basic::Signal::s: {
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
