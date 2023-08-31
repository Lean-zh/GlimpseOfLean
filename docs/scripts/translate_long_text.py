# translate long markdown text

from openai_api_call import Chat, num_tokens_from_messages
from random import choice
def split_mdtexts(text, find_ntoken=None, lowerbound=500, upperbound=800):
    """
    Split a long text into several texts, each with token
    number between lowerbound and upperbound.
    """
    if find_ntoken is None:
        find_ntoken = lambda content:num_tokens_from_messages(Chat(content).chat_log)
    lines = text.split("\n") # split by line
    texts, currenttext = [], ""
    incode = False # whether in code block
    for line in lines:
        if line.startswith("```"):
            incode = not incode
        currenttext += line + '\n'
        ntoken = find_ntoken(currenttext)
        if ntoken >= lowerbound and not incode:
            assert ntoken < upperbound, "Message token too large!"
            texts.append(currenttext)
            currenttext = ""
    if len(currenttext.strip()): # add the last text
        texts.append(currenttext)
    return texts

def translate_long_mdtext( text
                       , system=None
                       , prefix=""
                       , find_ntoken=None
                       , lowerbound=500
                       , upperbound=800
                       , showcost=True
                       , maxblock=10
                       , model=None):
    """
    Translate a long text into another long text.

    Args:
        text (str): The text to be translated.
        system (str): The system message to be used.
        prefix (str): The prefix to be added to the first message.
        find_ntoken (function): A function that takes a string and returns
            the number of tokens in the string.
        lowerbound (int): The lowerbound of the number of tokens in each message.
        upperbound (int): The upperbound of the number of tokens in each message.
        showcost (bool): Whether to show the cost of each response.
        maxblock (int): The maximum number of messages to be sent at a time.
        model (str): The model to be used.
    """
    texts = split_mdtexts(text, find_ntoken=find_ntoken, lowerbound=lowerbound, upperbound=upperbound)
    if not len(texts): return ""
    translated_texts = []

    chat = Chat()
    chat.model = model if model is not None else 'gpt-3.5-turbo-16k'
    # keep the first and last message
    hassystem = False
    if system is not None:
        chat.system(system)
        hassystem = True
    maxblock = max(3 + hassystem, maxblock)

    cost = 0
    texts[0] = prefix + texts[0]
    for text in texts:
        chat.user(text) # user message
        resp = chat.getresponse(max_requests=3)
        translated_texts.append(resp.content)
        if showcost:
            cost += resp.cost()
            print("Response cost:", resp.cost())
        if len(translated_texts) >= maxblock:
            pop_index = choice(range(1+hassystem, maxblock-1))
            chat.pop(pop_index)
    if showcost:
        print("Total cost:", cost)
    return "\n".join(translated_texts)