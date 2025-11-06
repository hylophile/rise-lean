build file:
    rm -f .lake/build/lib/lean/$(echo {{file}} | cut -d. -f1)*
    rm -f .lake/build/libegg*
    lake build {{file}}

watch *terms:
    watchexec --stop-timeout 0 --clear --quiet --exts lean "just infoview {{terms}}"

infoview *terms:
    lake build | just _search_all {{terms}}

_search_all *terms:
    #!/usr/bin/env -S awk -f
    BEGIN {
        IGNORECASE = 1
        n = split("{{terms}}", terms, " ")
    }
    /info: / {
        if (group && match_all(group)) {
            print group
            print ""
        }
        group = "\033[34m"$0"\033[m"
        next
    }
    { group = group "\n" $0 }
    END {
        if (group && match_all(group)) {
            print group
        }
    }
    function match_all(text) {
        for (i = 1; i <= n; i++) {
            if (text !~ terms[i]) {
                return 0
            }
        }
        return 1
    }
