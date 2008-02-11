/*  $Id$

    Part of CHR (Constraint Handling Rules)

    Author:        Tom Schrijvers
    E-mail:        Tom.Schrijvers@cs.kuleuven.be
    WWW:           http://www.swi-prolog.org
    Copyright (C): 2003-2004, K.U. Leuven

    This program is free software; you can redistribute it and/or
    modify it under the terms of the GNU General Public License
    as published by the Free Software Foundation; either version 2
    of the License, or (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU Lesser General Public
    License along with this library; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

    As a special exception, if you link this library with other files,
    compiled with a Free Software compiler, to produce an executable, this
    library does not by itself cause the resulting executable to be covered
    by the GNU General Public License. This exception does not however
    invalidate any other reasons why the executable file might be covered by
    the GNU General Public License.
*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Operator Priorities

:- op(1180, xfx, ==>).
:- op(1180, xfx, <=>).
:- op(1150, fx, constraints).
:- op(1150, fx, chr_constraint).
:- op(1150, fx, handler).
:- op(1150, fx, rules).
:- op(1100, xfx, \).
:- op(1200, xfx, @).			% values from hProlog
:- op(1190, xfx, pragma).		% values from hProlog
:- op( 500, yfx, #).			% values from hProlog
%:- op(1100, xfx, '|').
:- op(1150, fx, chr_type).
:- op(1130, xfx, --->).
:- op(1150, fx, (?)).
:- op(1150, fx, chr_declaration).
