# Copyright © 2001 by the Rectors and Visitors of the University of Virginia.
FROM ubuntu:latest
LABEL org.opencontainers.image.description="Reasoning and Computation"

ARG DEBIAN_FRONTEND=noninteractive
ARG NODE_VERSION=22.17.0
ARG YQ_VERSION=4.2.0
ARG TYPEDB_VERSION=2.28.0

ENV LANG=en_US.UTF-8 \
    LANGUAGE=en_US:en \
    LC_ALL=en_US.UTF-8 \
    PYTHONIOENCODING=utf-8 \
    SHELL=/bin/bash

SHELL ["/bin/bash", "-c"]
USER root

# ----- Base tools -----
RUN apt-get update --fix-missing && \
    apt-get install --no-install-recommends --assume-yes \
    build-essential \
    ca-certificates \
    curl \
    git \
    git-lfs \
    gnupg2 \
    less \
    libconfig-dev \
    libffi-dev \
    libssl-dev \
    locales \
    lsb-release \
    python3-dev \
    python3-pip \
    python3-venv \
    python-is-python3 \
    software-properties-common \
    unzip \
    vim \
    wget \
    zip \
    sudo && \
    locale-gen en_US.UTF-8 && \
    apt-get clean && rm -rf /var/lib/apt/lists/*

# Conventional locations for system-wide tools
RUN mkdir -p /opt/node 

# ----- Node.js (system-wide) -----
RUN curl -fsSLo /tmp/node.tar.xz "https://nodejs.org/dist/v${NODE_VERSION}/node-v${NODE_VERSION}-linux-x64.tar.xz" && \
    tar -xf /tmp/node.tar.xz -C /opt/node --strip-components=1 && \
    ln -sf /opt/node/bin/node /usr/local/bin/node && \
    ln -sf /opt/node/bin/npm  /usr/local/bin/npm && \
    ln -sf /opt/node/bin/npx  /usr/local/bin/npx && \
    rm -f /tmp/node.tar.xz

# ----- Create non-root user and workspace -----
RUN useradd -m -s /bin/bash dev && \
    usermod -aG sudo dev && \
    echo 'dev ALL=(ALL) NOPASSWD:ALL' > /etc/sudoers.d/dev && \
    chmod 0440 /etc/sudoers.d/dev && \
    mkdir -p /home/dev/app && chown -R dev:dev /home/dev/app

# Make the workspace path safe for Git even if mounted by host
RUN git config --global --add safe.directory /home/dev/

# ----- Switch to USER=dev for user-scoped installs -----
USER dev

# -- Change directory to /home/dev --
WORKDIR /home/dev

# Keep the devcontainer running so VS Code can attach
CMD ["sleep", "infinity"]