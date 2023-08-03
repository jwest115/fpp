// ======================================================================
// \title  EnumSerializableAc.hpp
// \author Generated by fpp-to-cpp
// \brief  hpp file for Enum struct
// ======================================================================

#ifndef EnumSerializableAc_HPP
#define EnumSerializableAc_HPP

#include "EEnumAc.hpp"
#include "FpConfig.hpp"
#include "Fw/Types/Serializable.hpp"
#include "Fw/Types/String.hpp"

class Enum :
  public Fw::Serializable
{

  public:

    // ----------------------------------------------------------------------
    // Types
    // ----------------------------------------------------------------------

    //! The array member types
    typedef M::E Type_of_eArr[3];

  public:

    // ----------------------------------------------------------------------
    // Constants
    // ----------------------------------------------------------------------

    enum {
      //! The size of the serial representation
      SERIALIZED_SIZE =
        M::E::SERIALIZED_SIZE +
        M::E::SERIALIZED_SIZE * 3
    };

  public:

    // ----------------------------------------------------------------------
    // Constructors
    // ----------------------------------------------------------------------

    //! Constructor (default value)
    Enum();

    //! Member constructor
    Enum(
        M::E::T e,
        const Type_of_eArr& eArr
    );

    //! Copy constructor
    Enum(
        const Enum& obj //!< The source object
    );

    //! Member constructor (scalar values for arrays)
    Enum(
        M::E::T e,
        M::E::T eArr
    );

  public:

    // ----------------------------------------------------------------------
    // Operators
    // ----------------------------------------------------------------------

    //! Copy assignment operator
    Enum& operator=(
        const Enum& obj //!< The source object
    );

    //! Equality operator
    bool operator==(
        const Enum& obj //!< The other object
    ) const;

    //! Inequality operator
    bool operator!=(
        const Enum& obj //!< The other object
    ) const;

#ifdef BUILD_UT

    //! Ostream operator
    friend std::ostream& operator<<(
        std::ostream& os, //!< The ostream
        const Enum& obj //!< The object
    );

#endif

  public:

    // ----------------------------------------------------------------------
    // Member functions
    // ----------------------------------------------------------------------

    //! Serialization
    Fw::SerializeStatus serialize(
        Fw::SerializeBufferBase& buffer //!< The serial buffer
    ) const;

    //! Deserialization
    Fw::SerializeStatus deserialize(
        Fw::SerializeBufferBase& buffer //!< The serial buffer
    );

#if FW_SERIALIZABLE_TO_STRING

    //! Convert struct to string
    void toString(
        Fw::StringBase& sb //!< The StringBase object to hold the result
    ) const;

#endif

    // ----------------------------------------------------------------------
    // Getter functions
    // ----------------------------------------------------------------------

    //! Get member e
    M::E::T gete() const
    {
      return this->e.e;
    }

    //! Get member eArr
    Type_of_eArr& geteArr()
    {
      return this->eArr;
    }

    //! Get member eArr (const)
    const Type_of_eArr& geteArr() const
    {
      return this->eArr;
    }

    // ----------------------------------------------------------------------
    // Setter functions
    // ----------------------------------------------------------------------

    //! Set all members
    void set(
        M::E::T e,
        const Type_of_eArr& eArr
    );

    //! Set member e
    void sete(M::E::T e);

    //! Set member eArr
    void seteArr(const Type_of_eArr& eArr);

  protected:

    // ----------------------------------------------------------------------
    // Member variables
    // ----------------------------------------------------------------------

    M::E e;
    M::E eArr[3];

};

#endif
