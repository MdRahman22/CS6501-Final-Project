# Source and target directories
SRC_DIR := Content
BUILD_DIR := src/Content

# Find all source files recursively
SRC_FILES := $(shell find $(SRC_DIR) -type f -name '*.lean')
# Derive corresponding output files with .md extension
#BUILD_FILES := $(patsubst $(SRC_DIR)/%, $(BUILD_DIR)/%.md, $(SRC_FILES))
BUILD_FILES := $(patsubst $(SRC_DIR)/%.lean,$(BUILD_DIR)/%.md,$(SRC_FILES))



# Default target: process all files
all: $(BUILD_FILES)

# Rule matches .lean → .md
$(BUILD_DIR)/%.md: $(SRC_DIR)/%.lean
	@mkdir -p $(dir $@)
	echo "Converting $< into $@"
	scripts/convert.hs $< $@
	
# Rule to process files and maintain directory structure
# $(BUILD_DIR)/%.md: $(SRC_DIR)/%
# 	@mkdir -p $(dir $@)  # Create the directory structure
# 	echo "Converting $< into $@"
# 	scripts/convert.hs $< $@

# Clean up the build directory
clean:
	rm -rf $(BUILD_DIR)

.PHONY: all clean

