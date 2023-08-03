// ======================================================================
// \title  ExplicitEnumAc.cpp
// \author Generated by fpp-to-cpp
// \brief  cpp file for Explicit enum
// ======================================================================

#include <cstring>
#include <limits>

#include "Fw/Types/Assert.hpp"
#include "ExplicitEnumAc.hpp"

namespace M {

  // ----------------------------------------------------------------------
  // Operators
  // ----------------------------------------------------------------------

  Explicit& Explicit ::
    operator=(const Explicit& obj)
  {
    this->e = obj.e;
    return *this;
  }

  Explicit& Explicit ::
    operator=(T e)
  {
    this->e = e;
    return *this;
  }

#ifdef BUILD_UT

  std::ostream& operator<<(std::ostream& os, const Explicit& obj) {
    Fw::String s;
    obj.toString(s);
    os << s;
    return os;
  }

#endif

  // ----------------------------------------------------------------------
  // Member functions
  // ----------------------------------------------------------------------

  bool Explicit ::
    isValid() const
  {
    return ((e >= X) && (e <= Y));
  }

  Fw::SerializeStatus Explicit ::
    serialize(Fw::SerializeBufferBase& buffer) const
  {
    const Fw::SerializeStatus status = buffer.serialize(
        static_cast<SerialType>(this->e)
    );
    return status;
  }

  Fw::SerializeStatus Explicit ::
    deserialize(Fw::SerializeBufferBase& buffer)
  {
    SerialType es;
    Fw::SerializeStatus status = buffer.deserialize(es);
    if (status == Fw::FW_SERIALIZE_OK) {
      this->e = static_cast<T>(es);
      if (!this->isValid()) {
        status = Fw::FW_DESERIALIZE_FORMAT_ERROR;
      }
    }
    return status;
  }

#if FW_SERIALIZABLE_TO_STRING

  void Explicit ::
    toString(Fw::StringBase& sb) const
  {
    Fw::String s;
    switch (e) {
      case X:
        s = "X";
        break;
      case Y:
        s = "Y";
        break;
      default:
        s = "[invalid]";
        break;
    }
    sb.format("%s (%" PRIu8 ")", s.toChar(), e);
  }

#elif FW_ENABLE_TEXT_LOGGING

  void Explicit ::
    toString(Fw::StringBase& sb) const
  {
    sb.format("%" PRIu8 "", e);
  }

#endif

}
