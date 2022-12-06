// ======================================================================
// \title  SingleElementArrayAc.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for SingleElement array
// ======================================================================

#include <cstdio>
#include <cstring>

#include "Fw/Types/Assert.hpp"
#include "Fw/Types/StringUtils.hpp"
#include "SingleElementArrayAc.hpp"

// ----------------------------------------------------------------------
// Constructors
// ----------------------------------------------------------------------

SingleElement ::
  SingleElement() :
    Serializable()
{
  // Construct using element-wise constructor
  *this = SingleElement(
    0
  );
}

SingleElement ::
  SingleElement(const ElementType (&a)[SIZE]) :
    Serializable()
{
  for (U32 index = 0; index < SIZE; index++) {
    this->elements[index] = a[index];
  }
}

SingleElement ::
  SingleElement(const ElementType& e1) :
    Serializable()
{
  this->elements[0] = e1;
}

SingleElement ::
  SingleElement(const SingleElement& obj) :
    Serializable()
{
  for (U32 index = 0; index < SIZE; index++) {
    this->elements[index] = obj.elements[index];
  }
}

// ----------------------------------------------------------------------
// Operators
// ----------------------------------------------------------------------

SingleElement::ElementType& SingleElement ::
  operator[](const U32 i)
{
  FW_ASSERT(i < SIZE);
  return this->elements[i];
}

const SingleElement::ElementType& SingleElement ::
  operator[](const U32 i) const
{
  FW_ASSERT(i < SIZE);
  return this->elements[i];
}

SingleElement& SingleElement ::
  operator=(const SingleElement& obj)
{
  if (this == &obj) {
    return *this;
  }

  for (U32 index = 0; index < SIZE; index++) {
    this->elements[index] = obj.elements[index];
  }
  return *this;
}

SingleElement& SingleElement ::
  operator=(const ElementType (&a)[SIZE])
{
  for (U32 index = 0; index < SIZE; index++) {
    this->elements[index] = a[index];
  }
  return *this;
}

SingleElement& SingleElement ::
  operator=(const ElementType& e)
{
  for (U32 index = 0; index < SIZE; index++) {
    this->elements[index] = e;
  }
  return *this;
}

bool SingleElement ::
  operator==(const SingleElement& obj) const
{
  for (U32 index = 0; index < SIZE; index++) {
    if (!((*this)[index] == obj[index])) {
      return false;
    }
  }
  return true;
}

bool SingleElement ::
  operator!=(const SingleElement& obj) const
{
  return !(*this == obj);
}

#ifdef BUILD_UT

std::ostream& operator<<(std::ostream& os, const SingleElement& obj) {
  Fw::String s;
  obj.toString(s);
  os << s;
  return os;
}

#endif

// ----------------------------------------------------------------------
// Member functions
// ----------------------------------------------------------------------

Fw::SerializeStatus SingleElement ::
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

Fw::SerializeStatus SingleElement ::
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

#if FW_ARRAY_TO_STRING || BUILD_UT

void SingleElement ::
  toString(Fw::StringBase& sb) const
{
  static const char *formatString = "[ "
    "%" PRIu32 " ]";

  char outputString[FW_ARRAY_TO_STRING_BUFFER_SIZE];
  (void) snprintf(
    outputString,
    FW_ARRAY_TO_STRING_BUFFER_SIZE,
    formatString,
    this->elements[0]
  );

  outputString[FW_ARRAY_TO_STRING_BUFFER_SIZE-1] = 0; // NULL terminate
  sb = outputString;
}

#endif