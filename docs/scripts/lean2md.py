import re, os
def lean2blocks(leancode, splitline='---SPLITLINE---'):
    # remove the inline sorry
    leancode = leancode.replace("/- inline sorry -/", "")
    # convert comment to plain text
    comments = re.findall(r"/-+ *(.*?) *-+/", leancode, re.S) # get comments
    comments = [comment.strip('\n') for comment in comments]
    codetxt = re.sub(r"/-+(.*?)-+/", splitline, leancode, flags=re.S) # convert comment to special token
    codes = [code.strip() for code in codetxt.split(splitline)]
    return comments, codes

def lean2markdown(leancode, splitline='---SPLITLINE---'):
    comments, codes = lean2blocks(leancode, splitline)
    # highlight plain text
    fcode = lambda code: "```lean\n" + code + "\n```\n"
    assert len(comments) == len(codes) + 1, "Error state"
    mdcode = fcode(codes[0])
    for comment, code in zip(comments, codes[1:]):
        mdcode += '\n' + comment + '\n'
        if not len(code):continue
        mdcode += '\n' + fcode(code)
    return mdcode

def findleanfiles(rootpath):
    return [os.path.join(root, file) for root, _, files in os.walk(rootpath)
                                     for file in files if file.endswith(".lean")]

def leanfile2mdfile(infile, outfile):
    """Convert lean file to markdown file"""
    with open(infile, "r", encoding="utf-8") as f:
        leancode = f.read()
    mdcode = lean2markdown(leancode)
    with open(outfile, "w", encoding="utf-8") as f:
        f.write(mdcode)