/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: t; c-basic-offset: 4 -*- */
/* QueueItemConflict.cc
 *
 * Copyright (C) 2000-2002 Ximian, Inc.
 * Copyright (C) 2005 SUSE Linux Products GmbH
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License,
 * version 2, as published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
 * 02111-1307, USA.
 */

#include "zypp/solver/detail/Types.h"

#include "zypp/solver/detail/QueueItemConflict.h"
#include "zypp/solver/detail/QueueItemBranch.h"
#include "zypp/solver/detail/QueueItemInstall.h"
#include "zypp/solver/detail/QueueItemUninstall.h"
#include "zypp/solver/detail/QueueItem.h"
#include "zypp/solver/detail/ResolverContext.h"
#include "zypp/solver/detail/ResolverInfoConflictsWith.h"
#include "zypp/solver/detail/ResolverInfoMisc.h"
#include "zypp/solver/detail/ResolverInfoObsoletes.h"
#include "zypp/CapFactory.h"
#include "zypp/CapSet.h"
#include "zypp/CapMatch.h"
#include "zypp/base/Logger.h"
#include "zypp/base/String.h"
#include "zypp/base/Gettext.h"

/////////////////////////////////////////////////////////////////////////
namespace zypp
{ ///////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////
  namespace solver
  { /////////////////////////////////////////////////////////////////////
    /////////////////////////////////////////////////////////////////////
    namespace detail
    { ///////////////////////////////////////////////////////////////////

using namespace std;

IMPL_PTR_TYPE(QueueItemConflict);

//---------------------------------------------------------------------------

ostream&
operator<<( ostream& os, const QueueItemConflict & item)
{
    os << "[Conflict: ";
    os << item._dep;
    os << ", Triggered by ";
    os << *(item._conflicting_item);
    if (item._actually_an_obsolete) os << ", Obsolete !";
    os << "]";
    return res;
}

//---------------------------------------------------------------------------

QueueItemConflict::QueueItemConflict (const ResPool *pool, const Capability & cap, PoolItem_Ref item)
    : QueueItem (QUEUE_ITEM_TYPE_CONFLICT, pool)
    , _capability (cap)
    , _conflicting_item (item)
    , _actually_an_obsolete (false)
{
}


QueueItemConflict::~QueueItemConflict()
{
}

//---------------------------------------------------------------------------

#if PHI

// on conflict, try to find upgrade candidates for the installed item triggering the conflict
// there are cases where upgrading prevents the conflict
// rc tends to uninstall the item
// phi tends to upgrade the item
// testcases: exercise-02conflict-08-test.xml, exercise-02conflict-09-test.xml

struct UpgradeCandidate : public resfilter::OnCapMatchCallbackFunctor
{
    PoolItem_Ref item; // the conflicting resolvable, used to filter upgrades with an identical resolvable
    PoolItemList upgrades;

    UpgradeCandidate (PoolItem_Ref pi)
	: item (pi)
    { }


    bool operator() (PoolItem_Ref & candidate, const Capability & cap)
    {
	if (!(item->equals (candidate)) 		// dont upgrade with ourselves
	    && candidate.status () == RESOLVABLE_STATUS_UNINSTALLED) {

	    info->upgrades.push_back (item);
	}
	return true;
    }
};

#endif  // PHI


//---------------------------------------------------------------------------------------

struct ConflictProcess : public resfilter::OnCapMatchCallbackFunctor
{
    const ResPool *pool;
    PoolItem_Ref conflict_issuer;			// the item which issues 'conflicts:'
    const Capability & conflict_capability;	// the capability mentioned in the 'conflicts'
    ResolverContext_Ptr context;
    QueueItemList & new_items;
    bool actually_an_obsolete;

    ConflictProcess (const ResPool *pl, PoolItem_Ref ci, const Capability & cc, ResolverContext_Ptr ct, QueueItemList & ni, bool ao)
	: pool (pl)
	, conflict_issuer (ci),
	, conflict_capability (cc)
	, context (ct),
	, new_items (ni)
	, actually_an_obsolete (ao)
    { }

    bool operator()( PoolItem_Ref & provider, const Capability & provides )
    {
    ResStatus status;
    ResolverInfo_Ptr log_info;
    CapFactory factory;

    DBG << "conflict_process_cb (resolvable[" << provider <<"], provides[" << provides << "], conflicts with [" <<
	      conflict_issuer << " conflicts: " << conflict_capability << endl;

    /* We conflict with ourself.  For the purpose of installing ourself, we
     * just ignore it, but it's Debian's way of saying that one and only one
     * item with this provide may exist on the system at a time. */

    if (conflict_issuer != NULL
	&& provider->equals (conflict_issuer)) {
	return true;
    }

    /* FIXME: This should probably be a GVersion capability. */
    /* Obsoletes don't apply to virtual provides, only the items
     * themselves.  A provide is "virtual" if it's not the same spec
     * as the item that's providing it.  This, of course, only
     * applies to RPM, since it's the only one with obsoletes right
     * now. */
    Capability capTest =  factory.parse ( provider->kind(),
	                                  provider->name(),
	                                  Rel::EQ,
	                                  provider->edition());

    if (actually_an_obsolete
	&& capTest.matches (provides) != CapMatch::yes )
    {
	return true;
    }

    status = provider.status();

    DBG << "conflict_process_cb (resolvable[" << provider << "]<" << status << ">" << endl;

    switch (status) {

	case RESOLVABLE_STATUS_INSTALLED:
	case RESOLVABLE_STATUS_TO_BE_INSTALLED_SOFT: {
	    QueueItemUninstall_Ptr uninstall;
	    ResolverInfo_Ptr log_info;

#if PHI
	    // maybe an upgrade can resolve the conflict ?
	    //        check if other item is available which upgrades

	    // find non-installed packages which provide the conflicting name

	    UpgradeCandidate upgrade_info (provider);

	    Capability maybe_upgrade_cap =  factory.parse ( provider->kind(),
	                                                    provider->name(),
	                                                    Rel::ANY,
	                                                    Edition::noedition );

	    // pool->foreachProvidingResItem (maybe_upgrade_dep, upgrade_candidates_cb, (void *)&upgrade_info);
	    Dep dep( Dep::PROVIDES );

	    invokeOnEach( pool->byCapabilityIndexBegin( maybe_upgrade_cap.index(), dep ),
			  pool->byCapabilityIndexEnd( maybe_upgrade_cap.index(), dep ),
			  resfilter::callOnCapMatchIn( dep, maybe_upgrade_cap, upgrade_info ) );

#endif

	    uninstall = new QueueItemUninstall (pool, provider, actually_an_obsolete ? QueueItemUninstall::OBSOLETE : QueueItemUninstall::CONFLICT);
	    uninstall->setDependency (conflict_capability);

	    if (actually_an_obsolete) {
	        uninstall->setDueToObsolete ();
	        log_info = new ResolverInfoObsoletes (provider, conflict_issuer);
	    } else {
	        uninstall->setDueToConflict ();
	        log_info = new ResolverInfoConflictsWith (provider, conflict_issuer);
	    }

	    uninstall->addInfo (log_info);

#if PHI
	    if (upgrade_info.upgrades.empty ()) {
#endif

	        info->new_items.push_back (uninstall);

#if PHI
	    }
	    else {
	        // there are upgrade candidates for the conflicting item
	        // branch to: 1. uninstall, 2. upgrade (for each upgrading item)

	        QueueItemBranch_Ptr branch = new QueueItemBranch (info->world);

	        branch->addItem (uninstall);			// try uninstall

	        for (PoolItemList::const_iterator iter = upgrade_info.upgrades.begin(); iter != upgrade_info.upgrades.end(); iter++) {
	            QueueItemInstall_Ptr upgrade = new QueueItemInstall (pool, *iter);
	            upgrade->setUpgrades (provider);
	            branch->addItem (upgrade);			// try upgrade
	        }
	        info->new_items.push_back (branch);
	    }
#endif

	    break;
	}

	case RESOLVABLE_STATUS_TO_BE_INSTALLED: {
	    ResolverInfoMisc_Ptr misc_info = new ResolverInfoMisc (RESOLVER_INFO_TYPE_CONFLICT_CANT_INSTALL, provider, RESOLVER_INFO_PRIORITY_VERBOSE, provides);

	    misc_info->flagAsError ();
	    if (info->conflict_issuer) {
	        misc_info->setOtherResItem (info->conflict_issuer);
		misc_info->setOtherCapability (info->conflict_capability);
	    }
	    info->context->addInfo (misc_info);

	    break;
	}

	case RESOLVABLE_STATUS_UNINSTALLED: {
	    info->context->setStatus (provider, RESOLVABLE_STATUS_TO_BE_UNINSTALLED);

	    ResolverInfoMisc_Ptr misc_info = new ResolverInfoMisc (RESOLVER_INFO_TYPE_CONFLICT_UNINSTALLABLE, provider, RESOLVER_INFO_PRIORITY_VERBOSE, provides);

	    misc_info->setOtherResItem (info->conflict_issuer);
	    misc_info->setOtherCapability (info->conflict_capability);

	    info->context->addInfo (misc_info);

	    break;
	}

	case RESOLVABLE_STATUS_TO_BE_UNINSTALLED:
	case RESOLVABLE_STATUS_TO_BE_UNINSTALLED_DUE_TO_OBSOLETE:
	    /* This is the easy case -- we do nothing. */
	    break;

	default:
	    abort();
    }

    return true;
}


bool
QueueItemConflict::process (ResolverContext_Ptr context, QueueItemList & new_items)
{
    DBG << "QueueItemConflict::process(" << this->asString() << ")" << endl;

    ConflictProcess info (pool(), _conflicting_item, _capability, context. new_items, actually_an_obsolete);

    // world()->foreachProvidingResItem (_capability, conflict_process_cb, (void *)&info);

    Dep dep( Dep::PROVIDES );
    invokeOnEach( pool()->byCapabilityIndexBegin( _capability.index(), dep ),
		  pool()->byCapabilityIndexEnd( _capability.index(), dep ),
		  resfilter::callOnCapMatchIn( dep, _capability, info ) );

    return true;
}


//---------------------------------------------------------------------------

QueueItem_Ptr
QueueItemConflict::copy (void) const
{
    QueueItemConflict_Ptr new_conflict = new QueueItemConflict (pool(), _capability, _conflicting_item);
    new_conflict->QueueItem::copy(this);

    // _actually_an_obsolete is not being copied !

    return new_conflict;
}


int
QueueItemConflict::cmp (QueueItem_constPtr item) const
{
    int cmp = this->compare (item);		// assures equal type
    if (cmp != 0)
	return cmp;

    QueueItemConflict_constPtr conflict = dynamic_pointer_cast<const QueueItemConflict>(item);
    if ( _capability != conflict->capability())
	cmp = -1;

    return cmp;
}

///////////////////////////////////////////////////////////////////
    };// namespace detail
    /////////////////////////////////////////////////////////////////////
    /////////////////////////////////////////////////////////////////////
  };// namespace solver
  ///////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////
};// namespace zypp
/////////////////////////////////////////////////////////////////////////
