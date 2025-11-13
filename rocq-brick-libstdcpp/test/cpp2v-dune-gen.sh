#!/bin/bash
#
# Copyright (C) 2020-2025 BlueRock Security, Inc.
#
# This software is distributed under the terms of the BedRock Open-Source License.
# See the LICENSE-BedRock file in the repository root for details.
#

usage() {
	cat >&2 <<-EOF
		usage: $(basename "$0") [ -t ] <filename>.<ext> <cpp2v-options> -- [ <clang-options> ]

		This will output (to stdout) dune rules for building <filename>.<ext>,
		passing <options> to cpp2v. Redirect output to dune.inc and
		load via dune's include.

		The output is filesystem-independent and <filename>.<ext> need not exist.
		Placing the output in <base>/dune.inc will transform
		<base>/<filename>.<ext> into <base>/<filename>_<ext>.v and
		<base>/<filename>_<ext>_names.v and (with \`-t\`)
		<base>/<filename>_<ext>_templates.v.
	EOF
	exit 1
}

outRule() {
	local indent fullName name ext
	indent="$1"
	fullName="$2"
	shift 2

	# The extension starts at the last dot:
	name="${fullName%.*}"
	if [ "$name" = "$fullName" ]; then
		echo -e "Error: filename '$fullName' has no extension\n" >&2
		usage
	fi
	ext="${fullName##*.}"

	local module="${name}_${ext}.v"
	local targ="${module}"
	local clang_options=""
	local universe=""
	if [ "$system" = 1 ]; then
		universe=" (universe)"
	fi
	local cpp2v="cpp2v -v %{input} -o ${module}"

	if [ "$gen_names" = 1 ]; then
		local names="${name}_${ext}_names.v"
		targ="${targ} ${names}"
		cpp2v="${cpp2v} -names ${names}"
	fi

	if [ "$templates" = 1 ]; then
		local templates="${name}_${ext}_templates.v"
		cpp2v="${cpp2v} --templates=${templates}"
		targ="$targ ${templates}"
	fi

	action="(run ${cpp2v} ${1+ $@} ${clang_options})"

	sed "s/^/${indent}/" <<-EOF
		(rule
		 (targets ${module}.stderr ${targ})
		 (alias test_ast)
		 (deps (:input ${name}.${ext}) (glob_files_rec ${prefix}*.hpp)${universe})
		 (action
		 	 (with-stderr-to ${module}.stderr ${action})))
		(alias (name srcs) (deps ${name}.${ext}))
	EOF
	# TODO: maybe drop @srcs alias, seems leftover from !2613
}

traverse() {
	local indent path firstDir rest
	indent="$1"
	path="$2"
	shift 2
	firstDir="${path%%/*}"
	rest="${path#*/}"
	if [ "$firstDir" = "$path" ]; then
		outRule "$indent" "$path" "$@"
	elif [ "$firstDir" = "." ]; then
		traverse "$indent" "$rest" "$@"
	else
		#echo DIR $firstDir
		#echo REST $rest
		echo "${indent}(subdir ${firstDir}"
		(cd "${firstDir}"; traverse " $indent" "$rest" "$@")
		echo "${indent})"
	fi
}

gen_names=0
templates=0
system=0
prefix="../"
while :
do
	case "$1" in
	-n)
		gen_names=1
		shift
		;;
	-t)
		templates=1
		shift
		;;
	-s)
		system=1
		shift
		;;
	-p)
		shift
		prefix="$1"
		shift
		;;
	--)
		shift
		break
		;;
	-*)
		usage
		;;
	*)
		break
		;;
	esac
done
[ $# -ge 1 ] || usage

path="$1"
shift

traverse "" "$path" "$@"

# vim:set noet sw=8:
