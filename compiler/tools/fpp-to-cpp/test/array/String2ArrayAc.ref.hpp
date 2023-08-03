// ======================================================================
// \title  String2ArrayAc.hpp
// \author Generated by fpp-to-cpp
// \brief  hpp file for String2 array
// ======================================================================

#ifndef String2ArrayAc_HPP
#define String2ArrayAc_HPP

#include "FpConfig.hpp"
#include "Fw/Types/Serializable.hpp"
#include "Fw/Types/String.hpp"

//! An array of strings with specified default value and format string
class String2 :
  public Fw::Serializable
{

  public:

    // ----------------------------------------------------------------------
    // StringSize80 class
    // ----------------------------------------------------------------------

    class StringSize80 :
      public Fw::StringBase
    {

      public:

        enum {
          //! The size of the string length plus the size of the string buffer
          SERIALIZED_SIZE = sizeof(FwBuffSizeType) + 80
        };

        //! Default constructor
        StringSize80();

        //! Char array constructor
        StringSize80(const char* src);

        //! String base constructor
        StringSize80(const Fw::StringBase& src);

        //! Copy constructor
        StringSize80(const StringSize80& src);

        //! Destructor
        ~StringSize80();

        //! Copy assignment operator
        StringSize80& operator=(const StringSize80& other);

        //! String base assignment operator
        StringSize80& operator=(const Fw::StringBase& other);

        //! char* assignment operator
        StringSize80& operator=(const char* other);

        //! Retrieves char buffer of string
        const char* toChar() const;

        NATIVE_UINT_TYPE getCapacity() const;

      private:

        char m_buf[80]; //!< Buffer for string storage

    };

  public:

    // ----------------------------------------------------------------------
    // Types
    // ----------------------------------------------------------------------

    //! The element type
    typedef StringSize80 ElementType;

  public:

    // ----------------------------------------------------------------------
    // Constants
    // ----------------------------------------------------------------------

    enum {
      //! The size of the array
      SIZE = 2,
      //! The size of the serial representation
      SERIALIZED_SIZE = SIZE * StringSize80::SERIALIZED_SIZE,
    };

  public:

    // ----------------------------------------------------------------------
    // Constructors
    // ----------------------------------------------------------------------

    //! Constructor (default value)
    String2();

    //! Constructor (user-provided value)
    String2(
        const ElementType (&a)[SIZE] //!< The array
    );

    //! Constructor (single element)
    String2(
        const ElementType& e //!< The element
    );

    //! Constructor (multiple elements)
    String2(
        const ElementType& e1, //!< Element 1
        const ElementType& e2 //!< Element 2
    );

    //! Copy Constructor
    String2(
        const String2& obj //!< The source object
    );

  public:

    // ----------------------------------------------------------------------
    // Operators
    // ----------------------------------------------------------------------

    //! Subscript operator
    ElementType& operator[](
        const U32 i //!< The subscript index
    );

    //! Const subscript operator
    const ElementType& operator[](
        const U32 i //!< The subscript index
    ) const;

    //! Copy assignment operator (object)
    String2& operator=(
        const String2& obj //!< The source object
    );

    //! Copy assignment operator (raw array)
    String2& operator=(
        const ElementType (&a)[SIZE] //!< The source array
    );

    //! Copy assignment operator (single element)
    String2& operator=(
        const ElementType& e //!< The element
    );

    //! Equality operator
    bool operator==(
        const String2& obj //!< The other object
    ) const;

    //! Inequality operator
    bool operator!=(
        const String2& obj //!< The other object
    ) const;

#ifdef BUILD_UT

    //! Ostream operator
    friend std::ostream& operator<<(
        std::ostream& os, //!< The ostream
        const String2& obj //!< The object
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

#if FW_ARRAY_TO_STRING

    //! Convert array to string
    void toString(
        Fw::StringBase& sb //!< The StringBase object to hold the result
    ) const;

#endif

  private:

    // ----------------------------------------------------------------------
    // Member variables
    // ----------------------------------------------------------------------

    //! The array elements
    ElementType elements[SIZE];

};

#endif
