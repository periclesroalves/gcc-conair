
// DO NOT EDIT THIS FILE - it is machine generated -*- c++ -*-

#ifndef __gnu_xml_libxmlj_dom_GnomeNamedNodeMap__
#define __gnu_xml_libxmlj_dom_GnomeNamedNodeMap__

#pragma interface

#include <java/lang/Object.h>
extern "Java"
{
  namespace gnu
  {
    namespace xml
    {
      namespace libxmlj
      {
        namespace dom
        {
            class GnomeNamedNodeMap;
        }
      }
    }
  }
  namespace org
  {
    namespace w3c
    {
      namespace dom
      {
          class Node;
      }
    }
  }
}

class gnu::xml::libxmlj::dom::GnomeNamedNodeMap : public ::java::lang::Object
{

public: // actually package-private
  GnomeNamedNodeMap(::java::lang::Object *, jint);
public:
  virtual ::org::w3c::dom::Node * getNamedItem(::java::lang::String *);
  virtual ::org::w3c::dom::Node * setNamedItem(::org::w3c::dom::Node *);
  virtual ::org::w3c::dom::Node * removeNamedItem(::java::lang::String *);
  virtual ::org::w3c::dom::Node * item(jint);
  virtual jint getLength();
  virtual ::org::w3c::dom::Node * getNamedItemNS(::java::lang::String *, ::java::lang::String *);
  virtual ::org::w3c::dom::Node * setNamedItemNS(::org::w3c::dom::Node *);
  virtual ::org::w3c::dom::Node * removeNamedItemNS(::java::lang::String *, ::java::lang::String *);
private:
  ::java::lang::Object * __attribute__((aligned(__alignof__( ::java::lang::Object)))) id;
  jint type;
public:
  static ::java::lang::Class class$;
};

#endif // __gnu_xml_libxmlj_dom_GnomeNamedNodeMap__
