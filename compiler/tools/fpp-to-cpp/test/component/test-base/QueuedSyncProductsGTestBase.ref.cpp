// ======================================================================
// \title  QueuedSyncProductsGTestBase.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for QueuedSyncProducts component Google Test harness base class
// ======================================================================

#include "test-base/QueuedSyncProductsGTestBase.hpp"

// ----------------------------------------------------------------------
// Construction and destruction
// ----------------------------------------------------------------------

QueuedSyncProductsGTestBase ::
  QueuedSyncProductsGTestBase(
      const char* const compName,
      const U32 maxHistorySize
  ) :
    QueuedSyncProductsTesterBase(compName, maxHistorySize)
{

}

QueuedSyncProductsGTestBase ::
  ~QueuedSyncProductsGTestBase()
{

}

// ----------------------------------------------------------------------
// From ports
// ----------------------------------------------------------------------

void QueuedSyncProductsGTestBase ::
  assertFromPortHistory_size(
      const char* const __callSiteFileName,
      const U32 __callSiteLineNumber,
      const U32 size
  ) const
{
  ASSERT_EQ(size, this->fromPortHistorySize)
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Total size of all from port histories\n"
    << "  Expected: " << size << "\n"
    << "  Actual:   " << this->fromPortHistorySize << "\n";
}

void QueuedSyncProductsGTestBase ::
  assert_from_noArgsOut_size(
      const char* const __callSiteFileName,
      const U32 __callSiteLineNumber,
      const U32 size
  ) const
{
  ASSERT_EQ(size, this->fromPortHistorySize_noArgsOut)
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Size of history for noArgsOut\n"
    << "  Expected: " << size << "\n"
    << "  Actual:   " << this->fromPortHistorySize_noArgsOut << "\n";
}

void QueuedSyncProductsGTestBase ::
  assert_from_noArgsReturnOut_size(
      const char* const __callSiteFileName,
      const U32 __callSiteLineNumber,
      const U32 size
  ) const
{
  ASSERT_EQ(size, this->fromPortHistorySize_noArgsReturnOut)
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Size of history for noArgsReturnOut\n"
    << "  Expected: " << size << "\n"
    << "  Actual:   " << this->fromPortHistorySize_noArgsReturnOut << "\n";
}

void QueuedSyncProductsGTestBase ::
  assert_from_typedOut_size(
      const char* const __callSiteFileName,
      const U32 __callSiteLineNumber,
      const U32 size
  ) const
{
  ASSERT_EQ(size, this->fromPortHistory_typedOut->size())
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Size of history for typedOut\n"
    << "  Expected: " << size << "\n"
    << "  Actual:   " << this->fromPortHistory_typedOut->size() << "\n";
}

void QueuedSyncProductsGTestBase ::
  assert_from_typedReturnOut_size(
      const char* const __callSiteFileName,
      const U32 __callSiteLineNumber,
      const U32 size
  ) const
{
  ASSERT_EQ(size, this->fromPortHistory_typedReturnOut->size())
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Size of history for typedReturnOut\n"
    << "  Expected: " << size << "\n"
    << "  Actual:   " << this->fromPortHistory_typedReturnOut->size() << "\n";
}

// ----------------------------------------------------------------------
// Data Product Request
// ----------------------------------------------------------------------

void QueuedSyncProductsGTestBase ::
  assertProductRequest_size(
      const char* const __callSiteFileName,
      const U32 __callSiteLineNumber,
      const U32 size
  ) const
{
  ASSERT_EQ(size, this->productRequestHistory->size())
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Size of product request history\n"
    << "  Expected: " << size << "\n"
    << "  Actual:   " << this->productRequestHistory->size() << "\n";
}

void QueuedSyncProductsGTestBase ::
  assertProductRequest(
      const char* const __callSiteFileName,
      const U32 __callSiteLineNumber,
      const U32 __index,
      FwDpIdType id,
      FwSizeType size
  ) const
{
  ASSERT_LT(__index, this->productRequestHistory->size())
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Index into product request history\n"
    << "  Expected: Less than size of product request history ("
    << this->productRequestHistory->size() << ")\n"
    << "  Actual:   " << __index << "\n";
  const DpRequest& e = this->productRequestHistory->at(__index);
  ASSERT_EQ(id, e.id)
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Id at index "
    << __index
    << " in product request history\n"
    << "  Expected: " << id << "\n"
    << "  Actual:   " << e.id << "\n";
  ASSERT_EQ(size, e.size)
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Size at index "
    << __index
    << " in product request history\n"
    << "  Expected: " << size << "\n"
    << "  Actual:   " << e.size << "\n";
}

// ----------------------------------------------------------------------
// Data Product Send
// ----------------------------------------------------------------------

void QueuedSyncProductsGTestBase ::
  assertProductSend_size(
      const char* const __callSiteFileName,
      const U32 __callSiteLineNumber,
      const U32 size
  ) const
{
  ASSERT_EQ(size, this->productSendHistory->size())
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Size of product send history\n"
    << "  Expected: " << size << "\n"
    << "  Actual:   " << this->productSendHistory->size() << "\n";
}

void QueuedSyncProductsGTestBase ::
  assertProductSend(
      const char* const __callSiteFileName,
      const U32 __callSiteLineNumber,
      const U32 __index,
      FwDpIdType id,
      FwDpPriorityType priority,
      const Fw::Time& timeTag,
      Fw::DpCfg::ProcType procType,
      const Fw::DpContainer::Header::UserData& userData,
      FwSizeType dataSize,
      Fw::Buffer& historyBuffer
  ) const
{
  ASSERT_LT(__index, this->productSendHistory->size())
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Index into product send history\n"
    << "  Expected: Less than size of product send history ("
    << this->productSendHistory->size() << ")\n"
    << "  Actual:   " << __index << "\n";
  const DpSend& e = this->productSendHistory->at(__index);
  // Set the history buffer output
  historyBuffer = e.buffer;
  // Check the container id
  ASSERT_EQ(e.id, id)
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Container ID at index " << index << " in product send history\n"
    << "  Expected: " << id << "\n"
    << "  Actual: " << e.id << "\n";
  // Check the header
  Fw::TestUtil::DpContainerHeader header;
  header.deserialize(__callSiteFileName, __callSiteLineNumber, historyBuffer);
  header.check(
      __callSiteFileName,
      __callSiteLineNumber,
      historyBuffer,
      id,
      priority,
      timeTag,
      procType,
      userData,
      dataSize
  );
}
