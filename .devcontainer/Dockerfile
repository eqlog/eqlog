ARG BASE_IMAGE
FROM ${BASE_IMAGE:-debian:testing}

USER root

RUN export DEBIAN_FRONTEND=noninteractive \
    && apt-get update \
    && apt-get install --yes \
        build-essential \
        pkg-config \
        git \
        curl \
        ca-certificates \
        sudo \
        locales \
        procps \
    && rm -rf /var/lib/apt/lists/*

ARG USER=user
ARG USER_ID=1000
ARG GROUP_ID=1000

ENV USER=${USER}

# Ensure the user and group exist, handling the case where the base image
# already provides them (possibly with a different uid/gid).
RUN if ! getent group ${USER} > /dev/null 2>&1; then \
        groupadd -g ${GROUP_ID} ${USER} || groupadd ${USER}; \
    fi && \
    if ! id -u ${USER} > /dev/null 2>&1; then \
        useradd -m -u ${USER_ID} -g ${USER} ${USER}; \
    fi && \
    echo "${USER} ALL=(ALL) NOPASSWD:ALL" >> /etc/sudoers

USER ${USER}

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/home/${USER}/.cargo/bin:${PATH}"
RUN rustup component add rust-analyzer

USER root
RUN mkdir /workspaces && chown ${USER}:${USER} /workspaces
USER ${USER}

RUN git clone https://github.com/eqlog/eqlog.git /workspaces/eqlog
WORKDIR /workspaces/eqlog

# Populate target/ so incremental builds are fast.
RUN cargo build --workspace \
    && cargo test --workspace --no-run
