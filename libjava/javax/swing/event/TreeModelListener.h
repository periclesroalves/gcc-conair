
// DO NOT EDIT THIS FILE - it is machine generated -*- c++ -*-

#ifndef __javax_swing_event_TreeModelListener__
#define __javax_swing_event_TreeModelListener__

#pragma interface

#include <java/lang/Object.h>
extern "Java"
{
  namespace javax
  {
    namespace swing
    {
      namespace event
      {
          class TreeModelEvent;
          class TreeModelListener;
      }
    }
  }
}

class javax::swing::event::TreeModelListener : public ::java::lang::Object
{

public:
  virtual void treeNodesChanged(::javax::swing::event::TreeModelEvent *) = 0;
  virtual void treeNodesInserted(::javax::swing::event::TreeModelEvent *) = 0;
  virtual void treeNodesRemoved(::javax::swing::event::TreeModelEvent *) = 0;
  virtual void treeStructureChanged(::javax::swing::event::TreeModelEvent *) = 0;
  static ::java::lang::Class class$;
} __attribute__ ((java_interface));

#endif // __javax_swing_event_TreeModelListener__
