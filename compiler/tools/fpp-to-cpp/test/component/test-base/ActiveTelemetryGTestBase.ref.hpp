// ======================================================================
// \title  ActiveTelemetryGTestBase.hpp
// \author Generated by fpp-to-cpp
// \brief  hpp file for ActiveTelemetry component Google Test harness base class
// ======================================================================

#ifndef ActiveTelemetryGTestBase_HPP
#define ActiveTelemetryGTestBase_HPP

#include "gtest/gtest.h"
#include "test-base/ActiveTelemetryTesterBase.hpp"

// ----------------------------------------------------------------------
// Macros for typed user from port history assertions
// ----------------------------------------------------------------------

#define ASSERT_FROM_PORT_HISTORY_SIZE(size) \
  this->assertFromPortHistory_size(__FILE__, __LINE__, size)

#define ASSERT_from_noArgsOut_SIZE(size) \
  this->assert_from_noArgsOut_size(__FILE__, __LINE__, size)

#define ASSERT_from_noArgsOut(index) \
  { \
    ASSERT_GT(this->fromPortHistory_noArgsOut->size(), static_cast<U32>(index)) \
      << "\n" \
      << __FILE__ << ":" << __LINE__ << "\n" \
      << "  Value:    Index into history of noArgsOut\n" \
      << "  Expected: Less than size of history (" \
      << this->fromPortHistory_noArgsOut->size() << ")\n" \
      << "  Actual:   " << index << "\n"; \
      const FromPortEntry_noArgsOut& _e = \
        this->fromPortHistory_noArgsOut->at(index); \
  }

#define ASSERT_from_typedOut_SIZE(size) \
  this->assert_from_typedOut_size(__FILE__, __LINE__, size)

#define ASSERT_from_typedOut(index, _u32, _f32, _b, _str1, _e, _a, _s) \
  { \
    ASSERT_GT(this->fromPortHistory_typedOut->size(), static_cast<U32>(index)) \
      << "\n" \
      << __FILE__ << ":" << __LINE__ << "\n" \
      << "  Value:    Index into history of typedOut\n" \
      << "  Expected: Less than size of history (" \
      << this->fromPortHistory_typedOut->size() << ")\n" \
      << "  Actual:   " << index << "\n"; \
      const FromPortEntry_typedOut& _e = \
        this->fromPortHistory_typedOut->at(index); \
    ASSERT_EQ(_u32, _e.u32) \
      << "\n" \
      << __FILE__ << ":" << __LINE__ << "\n" \
      << "  Value:    Value of argument u32 at index " \
      << index \
      << " in history of typedOut\n" \
      << "  Expected: " << _u32 << "\n" \
      << "  Actual:   " << _e.u32 << "\n"; \
    ASSERT_EQ(_f32, _e.f32) \
      << "\n" \
      << __FILE__ << ":" << __LINE__ << "\n" \
      << "  Value:    Value of argument f32 at index " \
      << index \
      << " in history of typedOut\n" \
      << "  Expected: " << _f32 << "\n" \
      << "  Actual:   " << _e.f32 << "\n"; \
    ASSERT_EQ(_b, _e.b) \
      << "\n" \
      << __FILE__ << ":" << __LINE__ << "\n" \
      << "  Value:    Value of argument b at index " \
      << index \
      << " in history of typedOut\n" \
      << "  Expected: " << _b << "\n" \
      << "  Actual:   " << _e.b << "\n"; \
    ASSERT_EQ(_str1, _e.str1) \
      << "\n" \
      << __FILE__ << ":" << __LINE__ << "\n" \
      << "  Value:    Value of argument str1 at index " \
      << index \
      << " in history of typedOut\n" \
      << "  Expected: " << _str1 << "\n" \
      << "  Actual:   " << _e.str1 << "\n"; \
    ASSERT_EQ(_e, _e.e) \
      << "\n" \
      << __FILE__ << ":" << __LINE__ << "\n" \
      << "  Value:    Value of argument e at index " \
      << index \
      << " in history of typedOut\n" \
      << "  Expected: " << _e << "\n" \
      << "  Actual:   " << _e.e << "\n"; \
    ASSERT_EQ(_a, _e.a) \
      << "\n" \
      << __FILE__ << ":" << __LINE__ << "\n" \
      << "  Value:    Value of argument a at index " \
      << index \
      << " in history of typedOut\n" \
      << "  Expected: " << _a << "\n" \
      << "  Actual:   " << _e.a << "\n"; \
    ASSERT_EQ(_s, _e.s) \
      << "\n" \
      << __FILE__ << ":" << __LINE__ << "\n" \
      << "  Value:    Value of argument s at index " \
      << index \
      << " in history of typedOut\n" \
      << "  Expected: " << _s << "\n" \
      << "  Actual:   " << _e.s << "\n"; \
  }

#define ASSERT_from_typedReturnOut_SIZE(size) \
  this->assert_from_typedReturnOut_size(__FILE__, __LINE__, size)

#define ASSERT_from_typedReturnOut(index, _u32, _f32, _b, _str2, _e, _a, _s) \
  { \
    ASSERT_GT(this->fromPortHistory_typedReturnOut->size(), static_cast<U32>(index)) \
      << "\n" \
      << __FILE__ << ":" << __LINE__ << "\n" \
      << "  Value:    Index into history of typedReturnOut\n" \
      << "  Expected: Less than size of history (" \
      << this->fromPortHistory_typedReturnOut->size() << ")\n" \
      << "  Actual:   " << index << "\n"; \
      const FromPortEntry_typedReturnOut& _e = \
        this->fromPortHistory_typedReturnOut->at(index); \
    ASSERT_EQ(_u32, _e.u32) \
      << "\n" \
      << __FILE__ << ":" << __LINE__ << "\n" \
      << "  Value:    Value of argument u32 at index " \
      << index \
      << " in history of typedReturnOut\n" \
      << "  Expected: " << _u32 << "\n" \
      << "  Actual:   " << _e.u32 << "\n"; \
    ASSERT_EQ(_f32, _e.f32) \
      << "\n" \
      << __FILE__ << ":" << __LINE__ << "\n" \
      << "  Value:    Value of argument f32 at index " \
      << index \
      << " in history of typedReturnOut\n" \
      << "  Expected: " << _f32 << "\n" \
      << "  Actual:   " << _e.f32 << "\n"; \
    ASSERT_EQ(_b, _e.b) \
      << "\n" \
      << __FILE__ << ":" << __LINE__ << "\n" \
      << "  Value:    Value of argument b at index " \
      << index \
      << " in history of typedReturnOut\n" \
      << "  Expected: " << _b << "\n" \
      << "  Actual:   " << _e.b << "\n"; \
    ASSERT_EQ(_str2, _e.str2) \
      << "\n" \
      << __FILE__ << ":" << __LINE__ << "\n" \
      << "  Value:    Value of argument str2 at index " \
      << index \
      << " in history of typedReturnOut\n" \
      << "  Expected: " << _str2 << "\n" \
      << "  Actual:   " << _e.str2 << "\n"; \
    ASSERT_EQ(_e, _e.e) \
      << "\n" \
      << __FILE__ << ":" << __LINE__ << "\n" \
      << "  Value:    Value of argument e at index " \
      << index \
      << " in history of typedReturnOut\n" \
      << "  Expected: " << _e << "\n" \
      << "  Actual:   " << _e.e << "\n"; \
    ASSERT_EQ(_a, _e.a) \
      << "\n" \
      << __FILE__ << ":" << __LINE__ << "\n" \
      << "  Value:    Value of argument a at index " \
      << index \
      << " in history of typedReturnOut\n" \
      << "  Expected: " << _a << "\n" \
      << "  Actual:   " << _e.a << "\n"; \
    ASSERT_EQ(_s, _e.s) \
      << "\n" \
      << __FILE__ << ":" << __LINE__ << "\n" \
      << "  Value:    Value of argument s at index " \
      << index \
      << " in history of typedReturnOut\n" \
      << "  Expected: " << _s << "\n" \
      << "  Actual:   " << _e.s << "\n"; \
  }

// ----------------------------------------------------------------------
// Macros for telemetry history assertions
// ----------------------------------------------------------------------

#define ASSERT_TLM_SIZE(size) \
  this->assertTlm_size(__FILE__, __LINE__, size)

#define ASSERT_TLM_ChannelU32Format_SIZE(size) \
  this->assertTlm_ChannelU32Format_size(__FILE__, __LINE__, size)

#define ASSERT_TLM_ChannelU32Format(index, value) \
  this->assertTlm_ChannelU32Format(__FILE__, __LINE__, index, value)

#define ASSERT_TLM_ChannelF32Format_SIZE(size) \
  this->assertTlm_ChannelF32Format_size(__FILE__, __LINE__, size)

#define ASSERT_TLM_ChannelF32Format(index, value) \
  this->assertTlm_ChannelF32Format(__FILE__, __LINE__, index, value)

#define ASSERT_TLM_ChannelStringFormat_SIZE(size) \
  this->assertTlm_ChannelStringFormat_size(__FILE__, __LINE__, size)

#define ASSERT_TLM_ChannelStringFormat(index, value) \
  this->assertTlm_ChannelStringFormat(__FILE__, __LINE__, index, value)

#define ASSERT_TLM_ChannelEnum_SIZE(size) \
  this->assertTlm_ChannelEnum_size(__FILE__, __LINE__, size)

#define ASSERT_TLM_ChannelEnum(index, value) \
  this->assertTlm_ChannelEnum(__FILE__, __LINE__, index, value)

#define ASSERT_TLM_ChannelArrayFreq_SIZE(size) \
  this->assertTlm_ChannelArrayFreq_size(__FILE__, __LINE__, size)

#define ASSERT_TLM_ChannelArrayFreq(index, value) \
  this->assertTlm_ChannelArrayFreq(__FILE__, __LINE__, index, value)

#define ASSERT_TLM_ChannelStructFreq_SIZE(size) \
  this->assertTlm_ChannelStructFreq_size(__FILE__, __LINE__, size)

#define ASSERT_TLM_ChannelStructFreq(index, value) \
  this->assertTlm_ChannelStructFreq(__FILE__, __LINE__, index, value)

#define ASSERT_TLM_ChannelU32Limits_SIZE(size) \
  this->assertTlm_ChannelU32Limits_size(__FILE__, __LINE__, size)

#define ASSERT_TLM_ChannelU32Limits(index, value) \
  this->assertTlm_ChannelU32Limits(__FILE__, __LINE__, index, value)

#define ASSERT_TLM_ChannelF32Limits_SIZE(size) \
  this->assertTlm_ChannelF32Limits_size(__FILE__, __LINE__, size)

#define ASSERT_TLM_ChannelF32Limits(index, value) \
  this->assertTlm_ChannelF32Limits(__FILE__, __LINE__, index, value)

#define ASSERT_TLM_ChannelF64_SIZE(size) \
  this->assertTlm_ChannelF64_size(__FILE__, __LINE__, size)

#define ASSERT_TLM_ChannelF64(index, value) \
  this->assertTlm_ChannelF64(__FILE__, __LINE__, index, value)

#define ASSERT_TLM_ChannelU32OnChange_SIZE(size) \
  this->assertTlm_ChannelU32OnChange_size(__FILE__, __LINE__, size)

#define ASSERT_TLM_ChannelU32OnChange(index, value) \
  this->assertTlm_ChannelU32OnChange(__FILE__, __LINE__, index, value)

#define ASSERT_TLM_ChannelEnumOnChange_SIZE(size) \
  this->assertTlm_ChannelEnumOnChange_size(__FILE__, __LINE__, size)

#define ASSERT_TLM_ChannelEnumOnChange(index, value) \
  this->assertTlm_ChannelEnumOnChange(__FILE__, __LINE__, index, value)

//! \class ActiveTelemetryGTestBase
//! \brief Auto-generated base for ActiveTelemetry component Google Test harness
class ActiveTelemetryGTestBase :
  public ActiveTelemetryTesterBase
{

  protected:

    // ----------------------------------------------------------------------
    // Construction and destruction
    // ----------------------------------------------------------------------

    //! Construct object ActiveTelemetryGTestBase
    ActiveTelemetryGTestBase(
        const char* const compName, //!< The component name
        const U32 maxHistorySize //!< The maximum size of each history
    );

    //! Destroy object ActiveTelemetryGTestBase
    ~ActiveTelemetryGTestBase();

  protected:

    // ----------------------------------------------------------------------
    // From ports
    // ----------------------------------------------------------------------

    //! From ports
    void assertFromPortHistory_size(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 size //!< The asserted size
    ) const;

    //! From port: noArgsOut
    void assert_from_noArgsOut_size(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 size //!< The asserted size
    ) const;

    //! From port: typedOut
    void assert_from_typedOut_size(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 size //!< The asserted size
    ) const;

    //! From port: typedReturnOut
    void assert_from_typedReturnOut_size(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 size //!< The asserted size
    ) const;

  protected:

    // ----------------------------------------------------------------------
    // Telemetry
    // ----------------------------------------------------------------------

    //! Assert the size of telemetry history
    void assertTlm_size(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 size //!< The asserted size
    ) const;

    //! Channel: ChannelU32Format
    void assertTlm_ChannelU32Format_size(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 size //!< The asserted size
    ) const;

    //! Channel: ChannelU32Format
    void assertTlm_ChannelU32Format(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 __index, //!< The index
        const U32 val //!< The channel value
    ) const;

    //! Channel: ChannelF32Format
    void assertTlm_ChannelF32Format_size(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 size //!< The asserted size
    ) const;

    //! Channel: ChannelF32Format
    void assertTlm_ChannelF32Format(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 __index, //!< The index
        const F32 val //!< The channel value
    ) const;

    //! Channel: ChannelStringFormat
    void assertTlm_ChannelStringFormat_size(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 size //!< The asserted size
    ) const;

    //! Channel: ChannelStringFormat
    void assertTlm_ChannelStringFormat(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 __index, //!< The index
        const char* const val //!< The channel value
    ) const;

    //! Channel: ChannelEnum
    void assertTlm_ChannelEnum_size(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 size //!< The asserted size
    ) const;

    //! Channel: ChannelEnum
    void assertTlm_ChannelEnum(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 __index, //!< The index
        const E& val //!< The channel value
    ) const;

    //! Channel: ChannelArrayFreq
    void assertTlm_ChannelArrayFreq_size(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 size //!< The asserted size
    ) const;

    //! Channel: ChannelArrayFreq
    void assertTlm_ChannelArrayFreq(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 __index, //!< The index
        const A& val //!< The channel value
    ) const;

    //! Channel: ChannelStructFreq
    void assertTlm_ChannelStructFreq_size(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 size //!< The asserted size
    ) const;

    //! Channel: ChannelStructFreq
    void assertTlm_ChannelStructFreq(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 __index, //!< The index
        const S& val //!< The channel value
    ) const;

    //! Channel: ChannelU32Limits
    void assertTlm_ChannelU32Limits_size(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 size //!< The asserted size
    ) const;

    //! Channel: ChannelU32Limits
    void assertTlm_ChannelU32Limits(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 __index, //!< The index
        const U32 val //!< The channel value
    ) const;

    //! Channel: ChannelF32Limits
    void assertTlm_ChannelF32Limits_size(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 size //!< The asserted size
    ) const;

    //! Channel: ChannelF32Limits
    void assertTlm_ChannelF32Limits(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 __index, //!< The index
        const F32 val //!< The channel value
    ) const;

    //! Channel: ChannelF64
    void assertTlm_ChannelF64_size(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 size //!< The asserted size
    ) const;

    //! Channel: ChannelF64
    void assertTlm_ChannelF64(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 __index, //!< The index
        const F64 val //!< The channel value
    ) const;

    //! Channel: ChannelU32OnChange
    void assertTlm_ChannelU32OnChange_size(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 size //!< The asserted size
    ) const;

    //! Channel: ChannelU32OnChange
    void assertTlm_ChannelU32OnChange(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 __index, //!< The index
        const U32 val //!< The channel value
    ) const;

    //! Channel: ChannelEnumOnChange
    void assertTlm_ChannelEnumOnChange_size(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 size //!< The asserted size
    ) const;

    //! Channel: ChannelEnumOnChange
    void assertTlm_ChannelEnumOnChange(
        const char* const __callSiteFileName, //!< The name of the file containing the call site
        const U32 __callSiteLineNumber, //!< The line number of the call site
        const U32 __index, //!< The index
        const E& val //!< The channel value
    ) const;

};

#endif
