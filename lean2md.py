import re, os
def lean2markdown(leancode, splitline="---SPLITLINE---"):
    # remove inline sorry
    leancode = leancode.replace("/- inline sorry -/", "")
    # starts with "/---  " and ends with "  ---/"
    comments = re.findall(r"/-+ *(.*?) *-+/", leancode, re.S)
    codetxt = re.sub(r"/-+(.*?)-+/", splitline, leancode, flags=re.S)
    codes = codetxt.split(splitline)
    # The file should be start with code(like import xxx)
    fcode = lambda code: "```lean\n" + code + "\n```\n"
    mdcode = fcode(codes[0].strip())
    for comment, code in zip(comments, codes[1:]):
        mdcode += '\n' + comment.strip('\n') + '\n'
        code = code.strip()
        if not len(code):continue
        mdcode += '\n' + fcode(code)
    return mdcode

def findleanfiles(rootpath):
    return [os.path.join(root, file) for root, _, files in os.walk(rootpath)
                      for file in files if file.endswith(".lean")]