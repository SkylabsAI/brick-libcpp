(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.initializer_list.spec.
(* The construction hint only fires on [Einitlist_std], so it is inert unless a
   proof actually builds an <<std::initializer_list>>; exporting it here saves
   every such client from importing it separately. *)
Require Export skylabs.brick.libstdcpp.initializer_list.hints.
