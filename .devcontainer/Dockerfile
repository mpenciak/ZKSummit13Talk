FROM ubuntu:noble

USER root

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install sudo git curl git bash-completion python3 python3-pip python3-requests -y && apt-get clean

RUN useradd -l -u 33333 -G sudo -md /home/gitpod -s /bin/bash -p gitpod gitpod \
    # passwordless sudo for users in the 'sudo' group
    && sed -i.bkp -e 's/%sudo\s\+ALL=(ALL\(:ALL\)\?)\s\+ALL/%sudo ALL=NOPASSWD:ALL/g' /etc/sudoers
USER gitpod
WORKDIR /home/gitpod
ENV HOME=/home/gitpod

SHELL ["/bin/bash", "-c"]

# gitpod bash prompt
RUN { echo && echo "PS1='\[\033[01;32m\]\u\[\033[00m\] \[\033[01;34m\]\w\[\033[00m\]\$(__git_ps1 \" (%s)\") $ '" ; } >> .bashrc

# install elan
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:v4.15.0

# install whichever toolchain mathlib is currently using
RUN . ~/.profile

# && elan toolchain install $(curl https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain)

# install neovim (for any lean.nvim user), via tarball since the appimage doesn't work for some reason, and jammy's version is ancient
# RUN curl -s -L https://github.com/neovim/neovim/releases/download/stable/nvim-linux-x86_64.tar.gz | tar xzf - && sudo mv nvim-linux-x86_64 /opt/nvim

ENV NARGO_HOME="/home/gitpod/.nargo"
ENV PATH="/home/gitpod/.nargo/bin:/home/gitpod/.bb:/home/gitpod/.local/bin:/home/gitpod/.elan/bin:/opt/nvim/bin:${PATH}"

# fix the infoview when the container is used on gitpod:
ENV VSCODE_API_VERSION="1.50.0"

# ssh to github once to bypass the unknown fingerprint warning
RUN ssh -o StrictHostKeyChecking=no github.com || true

RUN curl -L https://raw.githubusercontent.com/noir-lang/noirup/refs/heads/main/install | bash -s -- -y

RUN curl -L https://raw.githubusercontent.com/AztecProtocol/aztec-packages/refs/heads/master/barretenberg/bbup/install | bash -s -- -y

RUN mkdir -p $HOME/.lampe
RUN curl -k -L https://mpenciak.net/lampe --output $HOME/.lampe/lampe
RUN chmod +x $HOME/.lampe/lampe
RUN echo "export PATH=\$PATH:$HOME/.lampe" >> $HOME/.bashrc

RUN git clone https://github.com/mpenciak/ZKSummit13Talk $HOME/.zktalk

WORKDIR $HOME/.zktalk/lampe

RUN lake --verbose update
RUN lake --verbose exe cache get
RUN lake --verbose build

# run sudo once to suppress usage info
RUN sudo echo finished

