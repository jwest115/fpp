// ======================================================================
// \title  PassiveGetProductsGTestBase.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for PassiveGetProducts component Google Test harness base class
// ======================================================================

#include "test-base/PassiveGetProductsGTestBase.hpp"

// ----------------------------------------------------------------------
// Construction and destruction
// ----------------------------------------------------------------------

PassiveGetProductsGTestBase ::
  PassiveGetProductsGTestBase(
      const char* const compName,
      const U32 maxHistorySize
  ) :
    PassiveGetProductsTesterBase(compName, maxHistorySize)
{

}

PassiveGetProductsGTestBase ::
  ~PassiveGetProductsGTestBase()
{

}

// ----------------------------------------------------------------------
// From ports
// ----------------------------------------------------------------------

void PassiveGetProductsGTestBase ::
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

void PassiveGetProductsGTestBase ::
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

void PassiveGetProductsGTestBase ::
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

void PassiveGetProductsGTestBase ::
  assert_from_noArgsStringReturnOut_size(
      const char* const __callSiteFileName,
      const U32 __callSiteLineNumber,
      const U32 size
  ) const
{
  ASSERT_EQ(size, this->fromPortHistorySize_noArgsStringReturnOut)
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Size of history for noArgsStringReturnOut\n"
    << "  Expected: " << size << "\n"
    << "  Actual:   " << this->fromPortHistorySize_noArgsStringReturnOut << "\n";
}

void PassiveGetProductsGTestBase ::
  assert_from_typedAliasOut_size(
      const char* const __callSiteFileName,
      const U32 __callSiteLineNumber,
      const U32 size
  ) const
{
  ASSERT_EQ(size, this->fromPortHistory_typedAliasOut->size())
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Size of history for typedAliasOut\n"
    << "  Expected: " << size << "\n"
    << "  Actual:   " << this->fromPortHistory_typedAliasOut->size() << "\n";
}

void PassiveGetProductsGTestBase ::
  assert_from_typedAliasReturnOut_size(
      const char* const __callSiteFileName,
      const U32 __callSiteLineNumber,
      const U32 size
  ) const
{
  ASSERT_EQ(size, this->fromPortHistory_typedAliasReturnOut->size())
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Size of history for typedAliasReturnOut\n"
    << "  Expected: " << size << "\n"
    << "  Actual:   " << this->fromPortHistory_typedAliasReturnOut->size() << "\n";
}

void PassiveGetProductsGTestBase ::
  assert_from_typedAliasReturnStringOut_size(
      const char* const __callSiteFileName,
      const U32 __callSiteLineNumber,
      const U32 size
  ) const
{
  ASSERT_EQ(size, this->fromPortHistory_typedAliasReturnStringOut->size())
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Size of history for typedAliasReturnStringOut\n"
    << "  Expected: " << size << "\n"
    << "  Actual:   " << this->fromPortHistory_typedAliasReturnStringOut->size() << "\n";
}

void PassiveGetProductsGTestBase ::
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

void PassiveGetProductsGTestBase ::
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
// Data Product Get
// ----------------------------------------------------------------------

void PassiveGetProductsGTestBase ::
  assertProductGet_size(
      const char* const __callSiteFileName,
      const U32 __callSiteLineNumber,
      const U32 size
  ) const
{
  ASSERT_EQ(size, this->productGetHistory->size())
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Size of product get history\n"
    << "  Expected: " << size << "\n"
    << "  Actual:   " << this->productGetHistory->size() << "\n";
}

void PassiveGetProductsGTestBase ::
  assertProductGet(
      const char* const __callSiteFileName,
      const U32 __callSiteLineNumber,
      const U32 __index,
      FwDpIdType id,
      FwSizeType size
  ) const
{
  ASSERT_LT(__index, this->productGetHistory->size())
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Index into product get history\n"
    << "  Expected: Less than size of product get history ("
    << this->productGetHistory->size() << ")\n"
    << "  Actual:   " << __index << "\n";
  const DpGet& e = this->productGetHistory->at(__index);
  ASSERT_EQ(id, e.id)
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Id at index "
    << __index
    << " in product get history\n"
    << "  Expected: " << id << "\n"
    << "  Actual:   " << e.id << "\n";
  ASSERT_EQ(size, e.size)
    << "\n"
    << __callSiteFileName << ":" << __callSiteLineNumber << "\n"
    << "  Value:    Size at index "
    << __index
    << " in product get history\n"
    << "  Expected: " << size << "\n"
    << "  Actual:   " << e.size << "\n";
}

// ----------------------------------------------------------------------
// Data Product Send
// ----------------------------------------------------------------------

void PassiveGetProductsGTestBase ::
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

void PassiveGetProductsGTestBase ::
  assertProductSend(
      const char* const __callSiteFileName,
      const U32 __callSiteLineNumber,
      const U32 __index,
      FwDpIdType id,
      FwDpPriorityType priority,
      const Fw::Time& timeTag,
      Fw::DpCfg::ProcType::SerialType procTypes,
      const Fw::DpContainer::Header::UserData& userData,
      Fw::DpState dpState,
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
    << "  Value:    Container ID at index " << __index << " in product send history\n"
    << "  Expected: " << id << "\n"
    << "  Actual:   " << e.id << "\n";
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
      procTypes,
      userData,
      dpState,
      dataSize
  );
}
