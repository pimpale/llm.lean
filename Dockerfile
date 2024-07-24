# Use a base image with a recent version of Ubuntu
FROM ubuntu:22.04

# Install necessary dependencies
RUN apt-get update && apt-get install -y \
    curl \
    git \
    build-essential \
    cmake \
    libgmp-dev

# Install elan (Lean version manager)
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

# Add elan to PATH
ENV PATH="/root/.elan/bin:${PATH}"

# Set the working directory
WORKDIR /app

# Copy the project files
COPY . .

# Install project dependencies (if you have a lake.yaml file)
RUN lake update

# Build the project
RUN lake build

# Set the default command to run when the container starts
CMD ["lake", "build"]