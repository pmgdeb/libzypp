/*---------------------------------------------------------------------\
|                          ____ _   __ __ ___                          |
|                         |__  / \ / / . \ . \                         |
|                           / / \ V /|  _/  _/                         |
|                          / /__ | | | | | |                           |
|                         /_____||_| |_| |_|                           |
|                                                                      |
\---------------------------------------------------------------------*/
/** \file zypp/detail/ScriptImpl.cc
 *
*/

#include "zypp/detail/ScriptImpl.h"

using namespace std;

///////////////////////////////////////////////////////////////////
namespace zypp
{ /////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////
  namespace detail
  { /////////////////////////////////////////////////////////////////

    ///////////////////////////////////////////////////////////////////
    //
    //	CLASS NAME : ScriptImpl
    //
    ///////////////////////////////////////////////////////////////////

    /** Default ctor */
    ScriptImpl::ScriptImpl()
    {}
    /** Dtor */
    ScriptImpl::~ScriptImpl()
    {}

    std::string ScriptImpl::doScriptInlined() const
    { return _doScript; }

    std::string ScriptImpl::undoScriptInlined() const
    { return _undoScript; }


    /////////////////////////////////////////////////////////////////
  } // namespace detail
  ///////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////
} // namespace zypp
///////////////////////////////////////////////////////////////////
