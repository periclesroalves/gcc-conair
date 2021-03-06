/* NVList.java --
   Copyright (C) 2005 Free Software Foundation, Inc.

This file is part of GNU Classpath.

GNU Classpath is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2, or (at your option)
any later version.

GNU Classpath is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with GNU Classpath; see the file COPYING.  If not, write to the
Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
02110-1301 USA.

Linking this library statically or dynamically with other modules is
making a combined work based on this library.  Thus, the terms and
conditions of the GNU General Public License cover the whole
combination.

As a special exception, the copyright holders of this library give you
permission to link this library with independent modules to produce an
executable, regardless of the license terms of these independent
modules, and to copy and distribute the resulting executable under
terms of your choice, provided that you also meet, for each linked
independent module, the terms and conditions of the license of that
module.  An independent module is a module which is not derived from
or based on this library.  If you modify this library, you may extend
this exception to your version of the library, but you are not
obligated to do so.  If you do not wish to do so, delete this
exception statement from your version. */


package org.omg.CORBA;

import org.omg.CORBA.Any;
import org.omg.CORBA.Bounds;
import org.omg.CORBA.NamedValue;

/**
 * The named value list, used to define the parameters in the
 * {@link org.omg.CORBA.Request}. This class is also
 * used to hold the values of {@link Context}.
 *
 * @author Audrius Meskauskas (AudriusA@Bioinformatics.org)
 */
public abstract class NVList
{
  /**
   * Create and add a new named value object with null name,
   * null value and having given flags.
   * @param a_flags the flags, the normally expected values are
   * {@link org.omg.CORBA.ARG_IN#value},
   * {@link org.omg.CORBA.ARG_OUT#value} and
   * {@link org.omg.CORBA.ARG_INOUT#value} or 0.
   *
   * @return the created and added value.
   */
  public abstract NamedValue add(int a_flags);

  /**
   * Create and add the new named value object with the given
   * names, given flags and the null value.
   * @param a_name the name
   * @param a_flags the flags, the normally expected values are
   * {@link org.omg.CORBA.ARG_IN#value},
   * {@link org.omg.CORBA.ARG_OUT#value} and
   * {@link org.omg.CORBA.ARG_INOUT#value} or 0.
   *
   * @return the created and added value.
   */
  public abstract NamedValue add_item(String a_name, int a_flags);

  /**
   * Create and add the named value object with the given name,
   * value and flags.
   * @param a_name the name
   * @param a_value the value
   * @param a_flags the flags, the normally expected values are
   * {@link org.omg.CORBA.ARG_IN#value},
   * {@link org.omg.CORBA.ARG_OUT#value} and
   * {@link org.omg.CORBA.ARG_INOUT#value} or 0.
   *
   * @return the created object.
   */
  public abstract NamedValue add_value(String a_name, Any a_value, int a_flags);

  /**
   * Get the number of the present named value pairs.
   *
   * @return the number of objects in the list.
   */
  public abstract int count();

  /**
   * Get the item at the given index
   * @param at the index.
   *
   * @return the item at the index
   * @throws Bounds if the index is out of bounds.
   */
  public abstract NamedValue item(int at)
                           throws Bounds;

  /**
   * Remove the item at the given index
   * @param at the index
   * @throws Bounds if the index is out of bounds.
   */
  public abstract void remove(int at)
                       throws Bounds;
}
