// ======================================================================
// \title  PrimitiveI32ArrayAc.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for PrimitiveI32 array
// ======================================================================

#include <cstdio>
#include <cstring>

#include "Fw/Types/Assert.hpp"
#include "Fw/Types/StringUtils.hpp"
#include "PrimitiveI32ArrayAc.hpp"

namespace M {

  // ----------------------------------------------------------------------
  // Constructors
  // ----------------------------------------------------------------------

  PrimitiveI32 ::
    PrimitiveI32() :
      Serializable()
  {
    // Construct using element-wise constructor
    *this = PrimitiveI32(
      0,
      0,
      0
    );
  }

  PrimitiveI32 ::
    PrimitiveI32(const ElementType (&a)[SIZE]) :
      Serializable()
  {
    for (U32 index = 0; index < SIZE; index++) {
      this->elements[index] = a[index];
    }
  }

  PrimitiveI32 ::
    PrimitiveI32(const ElementType& e) :
      Serializable()
  {
    for (U32 index = 0; index < SIZE; index++) {
      this->elements[index] = e;
    }
  }

  PrimitiveI32 ::
    PrimitiveI32(
        const ElementType& e1,
        const ElementType& e2,
        const ElementType& e3
    ) :
      Serializable()
  {
    this->elements[0] = e1;
    this->elements[1] = e2;
    this->elements[2] = e3;
  }

  PrimitiveI32 ::
    PrimitiveI32(const PrimitiveI32& obj) :
      Serializable()
  {
    for (U32 index = 0; index < SIZE; index++) {
      this->elements[index] = obj.elements[index];
    }
  }

  // ----------------------------------------------------------------------
  // Operators
  // ----------------------------------------------------------------------

  PrimitiveI32::ElementType& PrimitiveI32 ::
    operator[](const U32 i)
  {
    FW_ASSERT(i < SIZE);
    return this->elements[i];
  }

  const PrimitiveI32::ElementType& PrimitiveI32 ::
    operator[](const U32 i) const
  {
    FW_ASSERT(i < SIZE);
    return this->elements[i];
  }

  PrimitiveI32& PrimitiveI32 ::
    operator=(const PrimitiveI32& obj)
  {
    if (this == &obj) {
      return *this;
    }

    for (U32 index = 0; index < SIZE; index++) {
      this->elements[index] = obj.elements[index];
    }
    return *this;
  }

  PrimitiveI32& PrimitiveI32 ::
    operator=(const ElementType (&a)[SIZE])
  {
    for (U32 index = 0; index < SIZE; index++) {
      this->elements[index] = a[index];
    }
    return *this;
  }

  PrimitiveI32& PrimitiveI32 ::
    operator=(const ElementType& e)
  {
    for (U32 index = 0; index < SIZE; index++) {
      this->elements[index] = e;
    }
    return *this;
  }

  bool PrimitiveI32 ::
    operator==(const PrimitiveI32& obj) const
  {
    for (U32 index = 0; index < SIZE; index++) {
      if (!((*this)[index] == obj[index])) {
        return false;
      }
    }
    return true;
  }

  bool PrimitiveI32 ::
    operator!=(const PrimitiveI32& obj) const
  {
    return !(*this == obj);
  }

#ifdef BUILD_UT

  std::ostream& operator<<(std::ostream& os, const PrimitiveI32& obj) {
    Fw::String s;
    obj.toString(s);
    os << s;
    return os;
  }

#endif

  // ----------------------------------------------------------------------
  // Member functions
  // ----------------------------------------------------------------------

  Fw::SerializeStatus PrimitiveI32 ::
    serialize(Fw::SerializeBufferBase& buffer) const
  {
    Fw::SerializeStatus status = Fw::FW_SERIALIZE_OK;
    for (U32 index = 0; index < SIZE; index++) {
      status = buffer.serialize((*this)[index]);
      if (status != Fw::FW_SERIALIZE_OK) {
        return status;
      }
    }
    return status;
  }

  Fw::SerializeStatus PrimitiveI32 ::
    deserialize(Fw::SerializeBufferBase& buffer)
  {
    Fw::SerializeStatus status = Fw::FW_SERIALIZE_OK;
    for (U32 index = 0; index < SIZE; index++) {
      status = buffer.deserialize((*this)[index]);
      if (status != Fw::FW_SERIALIZE_OK) {
        return status;
      }
    }
    return status;
  }

#if FW_ARRAY_TO_STRING

  void PrimitiveI32 ::
    toString(Fw::StringBase& sb) const
  {
    static const char *formatString = "[ "
      "%" PRIo32 " "
      "%" PRIo32 " "
      "%" PRIo32 " ]";

    char outputString[FW_ARRAY_TO_STRING_BUFFER_SIZE];
    (void) snprintf(
      outputString,
      FW_ARRAY_TO_STRING_BUFFER_SIZE,
      formatString,
      this->elements[0],
      this->elements[1],
      this->elements[2]
    );

    outputString[FW_ARRAY_TO_STRING_BUFFER_SIZE-1] = 0; // NULL terminate
    sb = outputString;
  }

#endif

}
