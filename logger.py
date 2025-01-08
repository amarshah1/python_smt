
log_enabled = False  # Default to logging disabled

def log(message, file="", indent=0):
    if log_enabled:
        if file == "":
            print(("    " * indent) + f"{message}")
        else:
            print(message, file = file)