/*---------------------------------------------------------------------\
|                          ____ _   __ __ ___                          |
|                         |__  / \ / / . \ . \                         |
|                           / / \ V /|  _/  _/                         |
|                          / /__ | | | | | |                           |
|                         /_____||_| |_| |_|                           |
|                                                                      |
\---------------------------------------------------------------------*/
/** \file zypp/detail/ResolvableImpl.cc
 *
*/
#include <iostream>
#include "zypp/base/Logger.h"

#include "zypp/ZYpp.h"
#include "zypp/ZYppFactory.h"

#include "zypp/base/Algorithm.h"
#include "zypp/detail/ResolvableImpl.h"
#include "zypp/capability/CapabilityImpl.h"
#include "zypp/capability/Capabilities.h"

using std::endl;

///////////////////////////////////////////////////////////////////
namespace zypp
{ /////////////////////////////////////////////////////////////////

  namespace
  {
    struct FilterUnwantedReq
    {
      bool operator()( const Capability & cap_r ) const
      {
        return cap_r.index().substr( 0, 7 ) == "rpmlib(";
      }
    };

    void filterUnwantedReq( const CapSet & from, CapSet & to )
    {
      to.clear();
      std::remove_copy_if( from.begin(), from.end(),
                           std::inserter( to, to.end() ),
                           FilterUnwantedReq() );
    }
  }

  namespace
  {
    struct FilterExtraDependency
    {
      Dependencies & deps;
      Dep _origin;

      FilterExtraDependency( Dependencies & d, const Dep & origin )
	: deps( d )
	, _origin( origin )
      { }

      bool operator()( const Capability & cap_r ) const
      {
	if ( isKind<capability::ModaliasCap>(cap_r) )
          {
            // in case cap provides a packagename, inject a SUPPLEMENTS.
            intrusive_ptr<const capability::ModaliasCap> cap( capability::asKind<capability::ModaliasCap>(cap_r) );
	    bool moved = false;
            if ( cap ) {
	      if (!cap->pkgname().empty() ) {
                deps[Dep::SUPPLEMENTS].insert( CapFactory().parse( ResTraits<Package>::kind, cap->pkgname() ) );
                deps[Dep::FRESHENS].insert(cap_r);
		moved = true;
	      }
	      else if (_origin == Dep::PROVIDES) {
                deps[Dep::SUPPLEMENTS].insert(cap_r);
		moved = true;
	      }
	    }
            return moved;	// strip from origin, if moved
          }

	if ( isKind<capability::HalCap>(cap_r) && _origin == Dep::PROVIDES )
          {
	    deps[Dep::SUPPLEMENTS].insert( cap_r );
            return true;	// strip from provides
          }

	if (cap_r.index().substr( 0, 7 ) != "locale(")
	    return false;

	CapFactory f;

	std::string locales( cap_r.index(), 7 );			// strip "locale("
	std::string::size_type pos = locales.find( ":" );		// colon given ?
	if (pos != std::string::npos) {
	    deps[Dep::SUPPLEMENTS].insert( f.parse( ResTraits<Package>::kind, std::string( locales, 0, pos ) ) );
	    locales.erase( 0, pos+1 );
	}
	pos = 0;
	std::string::size_type next = pos;
	while (pos < locales.size()) {
	    next = locales.find( ";", pos );			// look for ; separator
	    if (next == std::string::npos)
		next = locales.size()-1;			// none left, set next to end-1 (strip trailing ')' )

	    std::string loc( locales, pos, next-pos );
	    getZYpp()->availableLocale( Locale( loc ) );
	    deps[Dep::FRESHENS].insert( f.parse( ResTraits<Language>::kind, loc ) );
	    pos = next + 1;
	}
	return true;
      }
    };

    void filterExtraProvides( const Dependencies & from, Dependencies & to )
    {
      CapSet provides;
      FilterExtraDependency flp( to, Dep::PROVIDES );

      std::remove_copy_if( from[Dep::PROVIDES].begin(), from[Dep::PROVIDES].end(),
                           std::inserter( provides, provides.end() ),
                           flp );
      to[Dep::PROVIDES] = provides;
    }

    void filterExtraSupplements( const Dependencies & from, Dependencies & to )
    {
      CapSet supplements;
      to[Dep::SUPPLEMENTS].clear();
      
      FilterExtraDependency flp( to, Dep::SUPPLEMENTS );

      std::remove_copy_if( from[Dep::SUPPLEMENTS].begin(), from[Dep::SUPPLEMENTS].end(),
                           std::inserter( supplements, supplements.end() ),
                           flp );
      to[Dep::SUPPLEMENTS].insert(supplements.begin(), supplements.end());
    }      
  }

  Resolvable::Impl::Impl( const Kind & kind_r,
                          const NVRAD & nvrad_r )
  : _kind( kind_r )
  , _name( nvrad_r.name )
  , _edition( nvrad_r.edition )
  , _arch( nvrad_r.arch )
  , _deps( nvrad_r )
  {
    // check if we provide/supplements any extra ('locale(...)', 'modalias(...)', ...) tags
    // and split them up to freshens/supplements (except for SystemResObject)
      if ( _kind != ResTraits<SystemResObject>::kind ) {
	  filterExtraSupplements( nvrad_r, _deps );
	  filterExtraProvides( nvrad_r, _deps );
      }

    // assert self provides
    _deps[Dep::PROVIDES].insert( CapFactory()
                                 .parse( _kind, _name, Rel::EQ, _edition ) );

    // Filter 'rpmlib(...)' requirements (refill from nvrad_r)
    filterUnwantedReq( nvrad_r[Dep::PREREQUIRES], _deps[Dep::PREREQUIRES] );
    filterUnwantedReq( nvrad_r[Dep::REQUIRES], _deps[Dep::REQUIRES] );

    // assert all prerequires are in requires too
    _deps[Dep::REQUIRES].insert( _deps[Dep::PREREQUIRES].begin(),
                                 _deps[Dep::PREREQUIRES].end() );


    if ( _arch.empty() )
      dumpOn( WAR << "Has empty Arch: " ) << std::endl;
  }

  std::ostream & Resolvable::Impl::dumpOn( std::ostream & str ) const
  {
    return str << '[' << kind() << ']'
               << name() << '-' << edition() << '.' << arch();
  }

  /////////////////////////////////////////////////////////////////
} // namespace zypp
///////////////////////////////////////////////////////////////////
